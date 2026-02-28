// ФОРМАЛЬНА СПЕЦИФІКАЦІЯ ПРОГРАМНОЇ СИСТЕМИ "ЛІФТ" У DAFNY

// Ключова ідея інваріанту Valid():
//   Кожен публічний метод отримує Valid() як PRECONDITION (requires)
//   і зобов'язаний відновити Valid() як POSTCONDITION (ensures).
//   Таким чином Valid() — це "контракт стану", який ніколи не порушується.

module ElevatorValidPlus {

  // ====================================================================
  // 1) ПЕРЕЛІЧУВАНІ ТИПИ
  //
  //    Dafny datatype — це алгебраїчний тип даних (ADT).
  //    Кожен варіант є окремим конструктором без полів (enum-стиль).
  // ====================================================================

  // Напрямок руху кабіни ліфта
  datatype Direction = Up       // рух вгору
                     | Down     // рух вниз
                     | Idle     // кабіна нерухома (очікування)

  // Стан дверей кабіни
  datatype DoorState = Open     // двері відкриті (посадка/висадка)
                     | Closed   // двері зачинені (готовність до руху)

  // Напрямок виклику з поверхового майданчика
  datatype HallDir = HallUp     // пасажир хоче їхати ВГОРУ
                   | HallDown   // пасажир хоче їхати ВНИЗ

  // Режим роботи ліфта
  datatype Mode = Normal        // штатний режим
               | Emergency      // аварійний режим (рух заблокований)


  // ====================================================================
  // 2) КЛАС Elevator
  //
  //    У Dafny class — це єдиний об'єкт із станом (heap-allocated).
  //    Усі методи, що змінюють стан, оголошуються через "modifies this".
  // ====================================================================

  class Elevator {

    // ------------------------------------------------------------------
    // 2.1) КОНСТАНТИ СИСТЕМИ
    //
    //      "const" у Dafny — значення, задане у конструкторі
    //      та незмінне впродовж усього життя об'єкта.
    // ------------------------------------------------------------------

    const minFloor:     nat   // нижній поверх (включно), наприклад 0
    const maxFloor:     nat   // верхній поверх (включно), наприклад 10
    const maxDoorTicks: nat   // кількість тіків, протягом яких двері лишаються відкритими
                              // після відкриття. Після цього DoorTick() закриє двері.


    // ------------------------------------------------------------------
    // 2.2) ЗМІННІ СТАНУ
    //
    //      Ці поля утворюють "знімок" стану ліфта в будь-який момент часу.
    //      Їх сукупність описується інваріантом Valid().
    // ------------------------------------------------------------------

    var floor:     nat        // поточний поверх кабіни (minFloor ≤ floor ≤ maxFloor)
    var dir:       Direction  // поточний напрямок руху або Idle
    var door:      DoorState  // стан дверей: Open чи Closed
    var mode:      Mode       // Normal або Emergency

    // Множини активних запитів (set<nat> — множина натуральних чисел без дублікатів):
    var cabin:    set<nat>    // поверхи, натиснуті пасажирами ВСЕРЕДИНІ кабіни
    var hallUp:   set<nat>    // поверхи, де хтось натиснув кнопку "ВГОРУ" на майданчику
    var hallDown: set<nat>    // поверхи, де хтось натиснув кнопку "ВНИЗ" на майданчику

    var doorTicks: nat        // таймер відкритих дверей:
                              //   0              → двері Closed (або щойно закрились)
                              //   1..maxDoorTicks → двері Open, відраховуємо тіки

    var plan:      seq<nat>   // упорядкована черга поверхів для відвідування
                              // seq<nat> — послідовність (аналог масиву) натуральних чисел
                              // ІНВАРІАНТ: SeqToSet(plan) == cabin ∪ hallUp ∪ hallDown
                              //            і NoDups(plan) (усі елементи різні)


    // ====================================================================
    // 3) ПЕРЕТВОРЕННЯ seq<nat> → set<nat>
    //
    //    Проблема: у Dafny set-comprehension типу {x | x in plan} не завжди
    //    доводиться автоматично скінченним (Dafny вимагає явного свідчення).
    //    Рішення: використовуємо ІНДЕКСНИЙ comprehension із явним обмеженням
    //    "0 <= i < |s|" — верифікатор бачить скінченність по індексу.
    //
    //    SeqToSet([3, 5, 7]) == {3, 5, 7}
    //    SeqToSet([])        == {}
    // ====================================================================

    function SeqToSet(s: seq<nat>): set<nat>
    {
      // set i | умова :: вираз  — генератор множини
      // Читається: "множина всіх s[i], де i — індекс у s"
      set i | 0 <= i < |s| :: s[i]
    }


    // ====================================================================
    // 4) ЛЕМИ ПРО SeqToSet
    //
    //    Лема у Dafny — це метод, тіло якого є ДОКАЗОМ, а not кодом.
    //    Лема не змінює стан (немає "modifies"), лише переконує Z3 (SMT-solver)
    //    у правдивості деякого твердження.
    //
    //    Навіщо потрібні леми?
    //    Z3 може не "побачити" зв'язок між SeqToSet(s+[x]) і SeqToSet(s)+{x}
    //    сам по собі — особливо при рекурсії. Ми "розкладаємо" доведення
    //    вручну ("forall e | ... { ... }") і Z3 верифікує кожен крок.
    // ====================================================================

    // ──────────────────────────────────────────────────────────────────
    // Лема 4.1: Додавання елемента в кінець послідовності
    //           SeqToSet(s + [x]) == SeqToSet(s) ∪ {x}
    //
    //    Доводиться двосторонньою включеністю (A ⊆ B і B ⊆ A):
    //      → кожен e ∈ SeqToSet(s+[x]) є або в SeqToSet(s), або == x
    //      ← кожен e ∈ SeqToSet(s)∪{x} є в SeqToSet(s+[x])
    // ──────────────────────────────────────────────────────────────────
    lemma SeqToSetAppend(s: seq<nat>, x: nat)
      ensures SeqToSet(s + [x]) == SeqToSet(s) + {x}
    {
      // Напрям → : елемент з об'єднаної послідовності
      forall e | e in SeqToSet(s + [x])
        ensures e in SeqToSet(s) + {x}
      {
        // Знаходимо індекс i, де (s+[x])[i] == e (за означенням SeqToSet)
        var i :| 0 <= i < |s + [x]| && (s + [x])[i] == e;
        if i < |s| {
          assert s[i] == e;   // e стоїть у хвості s → входить до SeqToSet(s)
        } else {
          assert e == x;      // i == |s| → останній елемент — x
        }
      }

      // Напрям ← : елемент зі старої множини або {x}
      forall e | e in SeqToSet(s) + {x}
        ensures e in SeqToSet(s + [x])
      {
        if e in SeqToSet(s) {
          // Беремо той самий індекс з s — він дійсний і в s+[x]
          var i :| 0 <= i < |s| && s[i] == e;
          assert (s + [x])[i] == e;
        } else {
          // e == x знаходиться на позиції |s| у s+[x]
          assert (s + [x])[|s|] == x;
        }
      }
    }

    // ──────────────────────────────────────────────────────────────────
    // Лема 4.2: Розкладання послідовності з голови
    //           SeqToSet([h] + t) == {h} ∪ SeqToSet(t)
    //
    //    Корисна коли ми "знімаємо" перший елемент (голову) з послідовності
    //    і хочемо описати SeqToSet для залишку (хвоста t).
    // ──────────────────────────────────────────────────────────────────
    lemma SeqToSetCons(h: nat, t: seq<nat>)
      ensures SeqToSet([h] + t) == {h} + SeqToSet(t)
    {
      // Доведення аналогічне SeqToSetAppend, але для голови, а не хвоста
      forall e | e in SeqToSet([h] + t)
        ensures e in {h} + SeqToSet(t)
      {
        var i :| 0 <= i < |[h] + t| && ([h] + t)[i] == e;
        if i == 0 { assert e == h; }       // перша позиція — це h
        else      { assert t[i-1] == e; }  // решта — хвіст t
      }
      forall e | e in {h} + SeqToSet(t)
        ensures e in SeqToSet([h] + t)
      {
        if e == h { assert ([h] + t)[0] == h; }
        else {
          var i :| 0 <= i < |t| && t[i] == e;
          assert ([h] + t)[i + 1] == e;  // зсув на 1 через голову
        }
      }
    }

    // ──────────────────────────────────────────────────────────────────
    // Лема 4.3: Специфікація AddToPlan
    //
    //    Якщо x ВЖЕ є в послідовності → план не змінюється.
    //    Якщо x НЕМАє → SeqToSet зростає рівно на {x}.
    //
    //    Ця лема необхідна в методах AddCabinCall / AddHallCall,
    //    щоб верифікатор міг довести Valid() після зміни плану.
    // ──────────────────────────────────────────────────────────────────
    lemma AddToPlanSpec(s: seq<nat>, x: nat)
      ensures x in SeqToSet(s) ==>
                SeqToSet(AddToPlan(s, x)) == SeqToSet(s)
      ensures x !in SeqToSet(s) ==>
                SeqToSet(AddToPlan(s, x)) == SeqToSet(s) + {x}
    {
      if x in SeqToSet(s) {
        // AddToPlan повертає s без змін → SeqToSet теж без змін
        assert AddToPlan(s, x) == s;
      } else {
        // AddToPlan повертає s + [x] → застосовуємо лему 4.1
        assert AddToPlan(s, x) == s + [x];
        SeqToSetAppend(s, x);
      }
    }

    // ──────────────────────────────────────────────────────────────────
    // Лема 4.4: Специфікація RemoveFromPlan
    //
    //    Після видалення x із плану SeqToSet зменшується рівно на {x}.
    //    ВИМОГА: NoDups(s) — унікальність елементів.
    //    Без NoDups видалення першого входження x залишить інші копії,
    //    і SeqToSet(s) - {x} не буде правдивим.
    // ──────────────────────────────────────────────────────────────────
    lemma RemoveFromPlanSpec(s: seq<nat>, x: nat)
      requires NoDups(s)
      ensures  SeqToSet(RemoveFromPlan(s, x)) == SeqToSet(s) - {x}
    {
      if |s| == 0 {
        // Порожня послідовність: {} == {} - {x} = {} → тривіально.
      } else if s[0] == x {
        // Голова є x → RemoveFromPlan повертає s[1..] (хвіст без голови).
        // Треба показати SeqToSet(s[1..]) == SeqToSet(s) - {x}.
        forall e | e in SeqToSet(s[1..])
          ensures e in SeqToSet(s) - {x}
        {
          var i :| 0 <= i < |s[1..]| && s[1..][i] == e;
          assert s[i + 1] == e;
          // e != x бо NoDups: якби e == x, то s[0] == s[i+1] — дублікат!
          assert e != x by {
            if e == x { assert s[0] == s[i + 1]; }
          }
        }
        forall e | e in SeqToSet(s) - {x}
          ensures e in SeqToSet(s[1..])
        {
          var i :| 0 <= i < |s| && s[i] == e;
          assert i != 0 by { assert s[0] == x && e != x; }
          assert s[1..][i - 1] == e;  // зсув назад на 1
        }
      } else {
        // Голова != x → рекурсивно видаляємо з хвоста.
        // "RemoveFromPlan(s, x) == [s[0]] + RemoveFromPlan(s[1..], x)"
        RemoveFromPlanSpec(s[1..], x);         // IH: SeqToSet(r) == SeqToSet(s[1..]) - {x}
        var r := RemoveFromPlan(s[1..], x);
        SeqToSetCons(s[0], r);                 // SeqToSet([s[0]]+r) == {s[0]} + SeqToSet(r)
        SeqToSetCons(s[0], s[1..]);            // SeqToSet(s) == {s[0]} + SeqToSet(s[1..])
        // Зводимо разом:
        // SeqToSet([s[0]]+r) == {s[0]} + (SeqToSet(s[1..]) - {x})
        //                     == ({s[0]} + SeqToSet(s[1..])) - {x}  (бо s[0] != x)
        //                     == SeqToSet(s) - {x}
      }
    }

    // ──────────────────────────────────────────────────────────────────
    // Лема 4.5: RemoveFromPlan зберігає унікальність (NoDups)
    //
    //    Якщо до видалення послідовність мала унікальні елементи,
    //    то після видалення вона теж матиме унікальні елементи.
    //    Потрібна для підтримки інваріанту NoDups(plan).
    // ──────────────────────────────────────────────────────────────────
    lemma RemovePreservesNoDups(s: seq<nat>, x: nat)
      requires NoDups(s)
      ensures  NoDups(RemoveFromPlan(s, x))
    {
      if |s| == 0 {
        // Порожня → тривіально.
      } else if s[0] == x {
        // Видаляємо голову: залишається s[1..].
        // s[1..] є підпослідовністю NoDups-послідовності → теж NoDups.
        assert NoDups(s[1..]) by {
          forall i, j | 0 <= i < |s[1..]| && 0 <= j < |s[1..]| && i != j
            ensures s[1..][i] != s[1..][j]
          { assert s[i+1] != s[j+1]; }  // з NoDups(s)
        }
      } else {
        // Рекурсія на хвіст, потім доводимо NoDups для [s[0]] + r.
        RemovePreservesNoDups(s[1..], x);
        var r := RemoveFromPlan(s[1..], x);
        RemoveFromPlanSpec(s[1..], x);
        // SeqToSet(r) ⊆ SeqToSet(s[1..]), а s[0] ∉ SeqToSet(s[1..]) через NoDups(s).
        assert s[0] !in SeqToSet(s[1..]) by {
          forall k | 0 <= k < |s[1..]|
            ensures s[1..][k] != s[0]
          { assert s[k+1] != s[0]; }
        }
        assert NoDups([s[0]] + r) by {
          forall i, j | 0 <= i < |[s[0]] + r|
                     && 0 <= j < |[s[0]] + r| && i != j
            ensures ([s[0]] + r)[i] != ([s[0]] + r)[j]
          {
            if i == 0 {
              // Перший елемент — s[0], решта — з r ⊆ SeqToSet(s[1..])
              // s[0] ∉ SeqToSet(s[1..]) → не може збігатись із r[j-1]
              assert ([s[0]] + r)[j] == r[j-1];
              assert r[j-1] in SeqToSet(r);
              assert r[j-1] in SeqToSet(s[1..]);
            } else if j == 0 {
              assert ([s[0]] + r)[i] == r[i-1];
              assert r[i-1] in SeqToSet(r);
              assert r[i-1] in SeqToSet(s[1..]);
            } else {
              // Обидва з r: NoDups(r) забезпечує r[i-1] != r[j-1]
              assert r[i-1] != r[j-1];
            }
          }
        }
      }
    }

    // ──────────────────────────────────────────────────────────────────
    // Лема 4.6: AddToPlan зберігає унікальність (NoDups)
    //
    //    Якщо x вже в плані → план не змінився → NoDups тривіально.
    //    Якщо x новий → додаємо в кінець; треба довести x ∉ план,
    //    а всі старі елементи залишаються різними.
    // ──────────────────────────────────────────────────────────────────
    lemma AddToPlanPreservesNoDups(s: seq<nat>, x: nat)
      requires NoDups(s)
      ensures  NoDups(AddToPlan(s, x))
    {
      if x in SeqToSet(s) {
        assert AddToPlan(s, x) == s;  // план незмінний
      } else {
        assert AddToPlan(s, x) == s + [x];
        assert NoDups(s + [x]) by {
          forall i, j | 0 <= i < |s + [x]|
                     && 0 <= j < |s + [x]| && i != j
            ensures (s + [x])[i] != (s + [x])[j]
          {
            if i < |s| && j < |s| {
              // Обидва у старому s → NoDups(s)
              assert s[i] != s[j];
            } else if i == |s| {
              // i — новий елемент x; j — у s
              assert (s + [x])[i] == x;
              assert (s + [x])[j] == s[j];
              assert s[j] != x by { assert x !in SeqToSet(s); }
            } else {
              // j — новий елемент x; i — у s
              assert (s + [x])[j] == x;
              assert (s + [x])[i] == s[i];
              assert s[i] != x by { assert x !in SeqToSet(s); }
            }
          }
        }
      }
    }

    // ──────────────────────────────────────────────────────────────────
    // Лема 4.7: AddToPlan зберігає діапазон значень (InRange)
    //
    //    Якщо всі елементи s та x є у [minF, maxF],
    //    то всі елементи результату AddToPlan теж у [minF, maxF].
    //    Потрібна для підтримки інваріанту: plan[i] ∈ [minFloor, maxFloor].
    // ──────────────────────────────────────────────────────────────────
    lemma AddToPlanInRange(s: seq<nat>, x: nat, minF: nat, maxF: nat)
      requires forall i :: 0 <= i < |s| ==> minF <= s[i] <= maxF
      requires minF <= x <= maxF
      ensures  forall i :: 0 <= i < |AddToPlan(s, x)| ==>
                             minF <= AddToPlan(s, x)[i] <= maxF
    {
      // Обидва випадки: якщо x в s або ні — в обох випадках новий план
      // складається лише з елементів s та (може) x, усі в [minF, maxF].
      if x in SeqToSet(s) { assert AddToPlan(s, x) == s; }
      else                 { assert AddToPlan(s, x) == s + [x]; }
    }


    // ====================================================================
    // 5) ОСНОВНІ ДОПОМІЖНІ ФУНКЦІЇ ТА ПРЕДИКАТИ
    //
    //    "function" у Dafny — чиста функція (без побічних ефектів),
    //    може використовуватися у специфікаціях (requires/ensures).
    //    "predicate" — function що повертає bool (синтаксичний цукор).
    // ====================================================================

    // Чи є поверх f у допустимому діапазоні?
    // "reads this" — функція читає поля об'єкта (minFloor, maxFloor).
    predicate InRange(f: nat)
      reads this
    { minFloor <= f <= maxFloor }

    // Усі активні запити: об'єднання запитів з кабіни та майданчиків.
    // Це "розумна константа" для використання у специфікаціях.
    function Requests(): set<nat>
      reads this
    { cabin + hallUp + hallDown }

    // Чи є хоч один активний запит?
    function HasRequests(): bool
      reads this
    { Requests() != {} }

    // Чи є запит саме на поточному поверсі?
    // Використовується у DeterministicStep для визначення: відчиняти двері чи рухатись.
    function RequestedHere(): bool
      reads this
    { floor in Requests() }

    // Відстань між поверхами a та b (абсолютна різниця).
    // Використовується для пошуку найближчого запиту.
    function Dist(a: nat, b: nat): nat
    { if a <= b then b - a else a - b }


    // ──────────────────────────────────────────────────────────────────
    // NearestInSeq: рекурсивний пошук найближчого поверху до target
    //
    //    Алгоритм "турнір мінімуму":
    //      – база: один елемент → повернути його
    //      – крок: порівнюємо голову s[0] з рекурсивним результатом
    //              на хвості; повертаємо ближчий до target.
    //
    //    Чому не ":| "?
    //    Dafny вимагає для ":| " (choose) довести існування і унікальність
    //    в одному кроці, що важко для мінімуму на множині. Явний алгоритм
    //    значно простіший у верифікації.
    // ──────────────────────────────────────────────────────────────────
    function NearestInSeq(s: seq<nat>, target: nat): nat
      requires |s| > 0   // хоча б один елемент
    {
      if |s| == 1 then s[0]  // база: єдиний елемент
      else
        var rest := NearestInSeq(s[1..], target);  // рекурсія на хвіст
        // порівнюємо відстань голови і кращого з хвоста
        if Dist(target, s[0]) <= Dist(target, rest) then s[0] else rest
    }

    // Лема: результат NearestInSeq завжди є елементом вхідної послідовності.
    // Без цієї леми верифікатор не знає, чи є NearestRequest() в plan.
    lemma NearestInSeqMember(s: seq<nat>, target: nat)
      requires |s| > 0
      ensures  NearestInSeq(s, target) in SeqToSet(s)
    {
      if |s| == 1 {
        assert s[0] in SeqToSet(s);
      } else {
        NearestInSeqMember(s[1..], target);  // IH: rest ∈ SeqToSet(s[1..])
        var rest := NearestInSeq(s[1..], target);
        if Dist(target, s[0]) <= Dist(target, rest) {
          assert s[0] in SeqToSet(s);
        } else {
          // rest ∈ SeqToSet(s[1..]) ⊆ SeqToSet(s): передаємо через forall
          forall e | e in SeqToSet(s[1..]) ensures e in SeqToSet(s) {
            var i :| 0 <= i < |s[1..]| && s[1..][i] == e;
            assert s[i+1] == e;  // індекс у s зсунутий на 1
          }
        }
      }
    }

    // Лема: NearestInSeq повертає елемент з МІНІМАЛЬНОЮ відстанню до target.
    // Це підтверджує коректність алгоритму вибору напрямку руху.
    lemma NearestInSeqIsMin(s: seq<nat>, target: nat)
      requires |s| > 0
      ensures  forall q :: q in SeqToSet(s) ==>
                 Dist(target, NearestInSeq(s, target)) <= Dist(target, q)
    {
      if |s| == 1 {
        // Один елемент — завжди мінімальний.
      } else {
        NearestInSeqIsMin(s[1..], target);  // IH: rest мінімальний на хвості
        var rest   := NearestInSeq(s[1..], target);
        var chosen := NearestInSeq(s, target);
        forall q | q in SeqToSet(s)
          ensures Dist(target, chosen) <= Dist(target, q)
        {
          if q == s[0] {
            // chosen == s[0] (якщо s[0] ближче) або chosen == rest ≤ s[0].
          } else {
            // q ∈ SeqToSet(s[1..]): за IH rest ≤ q, а chosen ≤ rest.
            var i :| 0 <= i < |s| && s[i] == q;
            assert i > 0;
            assert s[1..][i-1] == q;
          }
        }
      }
    }

    // NearestRequest(): поверх з найближчим запитом до поточної позиції.
    // Використовується у DeterministicStep для вибору цілі руху.
    function NearestRequest(): nat
      requires Valid()
      requires HasRequests()  // лише якщо є запити (гарантує |plan| > 0)
      reads this
    {
      // |plan| > 0 гарантовано інваріантом:
      //   SeqToSet(plan) == Requests() і HasRequests() → Requests() != {}
      NearestInSeq(plan, floor)
    }

    // DistToNearest(): відстань до найближчого запиту (або 0 якщо запитів немає).
    // Корисна для потенційних функцій завершення (termination arguments).
    function DistToNearest(): nat
      requires Valid()
      reads this
    {
      if HasRequests() then Dist(floor, NearestRequest()) else 0
    }

    // NoDups(s): предикат унікальності елементів послідовності.
    //   forall i, j: якщо i ≠ j → s[i] ≠ s[j]
    // Гарантує, що plan не містить дублікатів (кожен поверх — один раз).
    predicate NoDups(s: seq<nat>)
    {
      forall i, j ::
        0 <= i < |s| && 0 <= j < |s| && i != j ==> s[i] != s[j]
    }

    // RemoveFromPlan: видаляє перше входження x із послідовності.
    //   [] → []
    //   [x, ...] → [...]         (видали голову)
    //   [h, ...] → [h] + Remove([...], x)  (рекурсія на хвіст)
    //
    // При NoDups перше входження є єдиним → коректне видалення.
    function RemoveFromPlan(s: seq<nat>, x: nat): seq<nat>
    {
      if |s| == 0 then []
      else if s[0] == x then s[1..]          // знайшли → відкидаємо голову
      else [s[0]] + RemoveFromPlan(s[1..], x) // не знайшли → зберігаємо голову
    }

    // AddToPlan: додає x в кінець лише якщо x ще не присутній.
    //   Гарантує NoDups після додавання.
    //   Якщо x вже є — повертає s без змін (ідемпотентна операція).
    function AddToPlan(s: seq<nat>, x: nat): seq<nat>
    {
      if x in SeqToSet(s) then s   // x вже є → нічого не змінюємо
      else s + [x]                  // x новий → додаємо в кінець черги
    }


    // ====================================================================
    // 6) ГЛОБАЛЬНИЙ ІНВАРІАНТ Valid()
    //
    //    Valid() — це "серце" специфікації. Кожен метод:
    //      1. ПРИЙМАЄ Valid() як precondition (requires Valid())
    //      2. ВІДНОВЛЮЄ Valid() як postcondition (ensures Valid())
    //
    //    Таким чином Valid() — це "незмінний контракт" між методами:
    //    усі методи залишають об'єкт у коректному стані.
    //
    //    Якщо Dafny верифікує модуль → Valid() гарантовано ніколи
    //    не порушується (за будь-якої послідовності викликів).
    // ====================================================================

    predicate Valid()
      reads this
    {
      // ── Базові обмеження конфігурації ──────────────────────────────
      minFloor <= maxFloor          // є хоча б один поверх
      && maxDoorTicks >= 1          // таймер дверей принаймні 1 тік

      // ── Поточний поверх у допустимому діапазоні ─────────────────────
      && InRange(floor)

      // ── Усі запити вказують на допустимі поверхи ────────────────────
      && (forall f :: f in cabin    ==> InRange(f))
      && (forall f :: f in hallUp   ==> InRange(f))
      && (forall f :: f in hallDown ==> InRange(f))

      // ── Семантичні обмеження на виклики з майданчика ────────────────
      // "вгору" лише з НЕ-верхнього поверху (нікуди їхати з даху)
      && (forall f :: f in hallUp   ==> f < maxFloor)
      // "вниз" лише з НЕ-нижнього поверху (нікуди їхати з підвалу)
      && (forall f :: f in hallDown ==> f > minFloor)

      // ── БЕЗПЕКА РУХУ: двері та рух взаємовиключні ───────────────────
      // Основна умова безпеки: якщо двері відкриті → кабіна стоїть.
      && (door == Open ==> dir == Idle)
      // Симетрично: якщо рухаємось → двері зачинені.
      && ((dir == Up || dir == Down) ==> door == Closed)

      // ── Аварійний режим: рух заборонений ────────────────────────────
      && (mode == Emergency ==> dir == Idle)

      // ── Узгодженість таймера дверей та їх стану ─────────────────────
      // Закриті двері: таймер обнулений.
      && (door == Closed ==> doorTicks == 0)
      // Відкриті двері: таймер ненульовий і в межах [1, maxDoorTicks].
      && (door == Open   ==> 1 <= doorTicks <= maxDoorTicks)

      // ── Коректність плану обслуговування ────────────────────────────
      // Кожен елемент плану — допустимий поверх.
      && (forall i :: 0 <= i < |plan| ==> InRange(plan[i]))
      // Немає дублікатів у плані.
      && NoDups(plan)
      // КЛЮЧОВИЙ інваріант узгодженості: план == об'єднання всіх запитів.
      // SeqToSet(plan) є впорядкованим "зображенням" множини Requests().
      && SeqToSet(plan) == Requests()
    }


    // ====================================================================
    // 7) КОНСТРУКТОР
    //
    //    Ініціалізує ліфт у повністю коректному стані.
    //    Postconditions гарантують, що після побудови Valid() виконується
    //    і всі поля мають очікувані початкові значення.
    // ====================================================================

    constructor(minF: nat, maxF: nat, start: nat, maxTicks: nat)
      // Preconditions: мінімальні вимоги до вхідних параметрів.
      requires minF <= maxF       // коректний діапазон поверхів
      requires minF <= start <= maxF  // стартовий поверх у діапазоні
      requires maxTicks >= 1     // таймер дверей принаймні 1
      ensures Valid()
      ensures minFloor == minF && maxFloor == maxF && maxDoorTicks == maxTicks
      ensures floor == start
      ensures dir == Idle && door == Closed && mode == Normal
      ensures cabin == {} && hallUp == {} && hallDown == {}
      ensures doorTicks == 0 && plan == []
    {
      // Ініціалізуємо всі константи і поля в порядку,
      // щоб Valid() виконувалась після завершення конструктора.
      minFloor     := minF;
      maxFloor     := maxF;
      maxDoorTicks := maxTicks;
      floor        := start;
      dir          := Idle;       // кабіна нерухома при старті
      door         := Closed;     // двері зачинені при старті
      mode         := Normal;     // штатний режим
      cabin        := {};         // жодних запитів
      hallUp       := {};
      hallDown     := {};
      doorTicks    := 0;          // таймер обнулений (двері закриті)
      plan         := [];         // план порожній (немає запитів)
    }


    // ====================================================================
    // 8) РЕЄСТРАЦІЯ ЗАПИТІВ
    //
    //    Ці методи викликаються, коли пасажири натискають кнопки.
    //    Кожен метод додає запит у відповідну множину та оновлює plan.
    // ====================================================================

    // ──────────────────────────────────────────────────────────────────
    // AddCabinCall: пасажир усередині кабіни натиснув кнопку поверху f.
    //
    //    Наприклад: їдучи в ліфті, пасажир натиснув "5" → f == 5.
    //    Метод: додає f до cabin та до plan (якщо ще не присутнє).
    //
    //    ПОРЯДОК ОПЕРАЦІЙ (критично для верифікації):
    //      1. Викликаємо леми ДО мутації (вони посилаються на поточний стан)
    //      2. Обчислюємо newPlan (чиста функція, не змінює стан)
    //      3. Оновлюємо cabin та plan
    //
    //    Чому обчислення newPlan перед мутацією?
    //    Якби ми спочатку змінили cabin, то Valid() тимчасово порушився б
    //    (SeqToSet(plan) != Requests()), і Dafny не міг би верифікувати.
    // ──────────────────────────────────────────────────────────────────
    method AddCabinCall(f: nat)
      requires Valid()
      requires InRange(f)   // f повинен бути у допустимому діапазоні
      modifies this         // метод може змінювати поля об'єкта
      ensures Valid()
      ensures cabin     == old(cabin) + {f}          // f з'явився в cabin
      ensures hallUp    == old(hallUp) && hallDown == old(hallDown)  // без змін
      ensures plan      == AddToPlan(old(plan), f)   // plan оновлено
      ensures floor     == old(floor)  && dir  == old(dir)
      ensures door      == old(door)   && mode == old(mode)
      ensures doorTicks == old(doorTicks)
    {
      // Крок 1: Попередньо виклик лем (підказки для Z3).
      // Леми "розповідають" верифікатору факти про результат AddToPlan,
      // які Z3 не може вивести сам із визначення функції.
      AddToPlanSpec(plan, f);           // SeqToSet змінюється коректно
      AddToPlanPreservesNoDups(plan, f); // NoDups зберігається
      AddToPlanInRange(plan, f, minFloor, maxFloor); // елементи в діапазоні

      // Крок 2: Обчислити новий план як чисте значення (до мутації стану).
      var newPlan := AddToPlan(plan, f);

      // Крок 3: Мутуємо стан — спочатку cabin, потім plan.
      cabin := cabin + {f};
      plan  := newPlan;

      // Перевірка (assertion): Z3 може сам перевірити це після лем вище.
      assert SeqToSet(plan) == Requests();
    }

    // AddHallCall: пасажир на поверсі f натиснув кнопку напрямку d.
    //
    //    Наприклад: на 3-му поверсі пасажир натиснув "вниз" → f==3, d==HallDown.
    //    Вимоги: d==HallUp → f не верхній; d==HallDown → f не нижній.
    //    Метод: додає f до hallUp або hallDown та до plan.
    method AddHallCall(f: nat, d: HallDir)
      requires Valid()
      requires InRange(f)
      // Семантичні обмеження: на верхньому поверсі не можна їхати вгору,
      // на нижньому — вниз (нема куди).
      requires d == HallUp   ==> f < maxFloor
      requires d == HallDown ==> f > minFloor
      modifies this
      ensures Valid()
      ensures cabin     == old(cabin)
      ensures plan      == AddToPlan(old(plan), f)
      ensures floor     == old(floor) && dir  == old(dir)
      ensures door      == old(door)  && mode == old(mode)
      ensures doorTicks == old(doorTicks)
      ensures (d == HallUp ==>
                 hallUp   == old(hallUp) + {f} &&
                 hallDown == old(hallDown))
      ensures (d == HallDown ==>
                 hallDown == old(hallDown) + {f} &&
                 hallUp   == old(hallUp))
    {
      // Ті самі леми що і в AddCabinCall
      AddToPlanSpec(plan, f);
      AddToPlanPreservesNoDups(plan, f);
      AddToPlanInRange(plan, f, minFloor, maxFloor);

      // Обчислити новий план ДО мутації hall-множин (та сама причина)
      var newPlan := AddToPlan(plan, f);

      // Оновлюємо відповідну множину залежно від напрямку
      if d == HallUp {
        hallUp := hallUp + {f};    // запит "вгору" з поверху f
      } else {
        hallDown := hallDown + {f}; // запит "вниз" з поверху f
      }
      plan := newPlan;

      assert SeqToSet(plan) == Requests();
    }


    // ====================================================================
    // 9) АВАРІЙНИЙ РЕЖИМ
    //
    //    SetEmergency(true)  → переходимо в Emergency, зупиняємо кабіну.
    //    SetEmergency(false) → повертаємось у Normal.
    //
    //    В аварійному режимі: рух заборонений (dir == Idle),
    //    але план, запити та стан дверей НЕ змінюються.
    //    Після відновлення ліфт продовжить обслуговувати запити.
    // ====================================================================

    method SetEmergency(on: bool)
      requires Valid()
      modifies this
      ensures Valid()
      ensures (on  ==> mode == Emergency && dir == Idle)
      ensures (!on ==> mode == Normal)
      // Усе інше залишається без змін
      ensures floor     == old(floor)    && door == old(door)
      ensures cabin     == old(cabin)    && hallUp  == old(hallUp)
      ensures hallDown  == old(hallDown) && doorTicks == old(doorTicks)
      ensures plan == old(plan)
    {
      if on {
        mode := Emergency;
        dir  := Idle;   // БЕЗПЕКА: зупиняємо кабіну негайно
      } else {
        mode := Normal;
        // dir залишається Idle — контролер вирішить далі у DeterministicStep
      }
    }

    // 10) КЕРУВАННЯ ДВЕРИМА

    // ──────────────────────────────────────────────────────────────────
    // OpenDoor: відчиняємо двері.
    //
    //    ВИМОГА: dir == Idle (кабіна стоїть — безпека!).
    //    Встановлює doorTicks = maxDoorTicks для зворотного відліку.
    //    Після maxDoorTicks тіків DoorTick() автоматично зачинить двері.
    // ──────────────────────────────────────────────────────────────────
    method OpenDoor()
      requires Valid()
      requires dir == Idle   // БЕЗПЕКА: не відчиняти під час руху!
      modifies this
      ensures Valid()
      ensures door      == Open
      ensures doorTicks == maxDoorTicks  // починаємо відлік
      ensures floor == old(floor) && dir  == old(dir)  && mode == old(mode)
      ensures cabin == old(cabin) && hallUp == old(hallUp) && hallDown == old(hallDown)
      ensures plan  == old(plan)
    {
      door      := Open;
      doorTicks := maxDoorTicks;  // встановлюємо таймер
    }

    // ──────────────────────────────────────────────────────────────────
    // CloseDoor: примусово зачиняємо двері (незалежно від таймера).
    //
    //    Наприклад: кнопка "зачинити двері" або аварійне закриття.
    //    Обнуляємо doorTicks (двері Closed → тики == 0).
    // ──────────────────────────────────────────────────────────────────
    method CloseDoor()
      requires Valid()
      modifies this
      ensures Valid()
      ensures door      == Closed
      ensures doorTicks == 0
      ensures floor == old(floor) && dir  == old(dir)  && mode == old(mode)
      ensures cabin == old(cabin) && hallUp == old(hallUp) && hallDown == old(hallDown)
      ensures plan  == old(plan)
    {
      door      := Closed;
      doorTicks := 0;
    }

    // ──────────────────────────────────────────────────────────────────
    // DoorTick: один тік часу при відкритих дверях.
    //
    //    Якщо doorTicks == 1 → таймер спливає → автозакриття.
    //    Якщо doorTicks > 1  → декрементуємо таймер, двері лишаються Open.
    //
    //    Викликається кожен тік часу у DeterministicStep (крок 2).
    // ──────────────────────────────────────────────────────────────────
    method DoorTick()
      requires Valid()
      requires door == Open     // тікати лише при відкритих дверях
      modifies this
      ensures Valid()
      ensures cabin    == old(cabin)    && hallUp  == old(hallUp)
      ensures hallDown == old(hallDown) && plan    == old(plan)
      ensures floor == old(floor) && dir == old(dir) && mode == old(mode)
      // Поведінка залежить від значення таймера:
      ensures (old(doorTicks) == 1 ==> door == Closed && doorTicks == 0)
      ensures (old(doorTicks) >  1 ==> door == Open   && doorTicks == old(doorTicks) - 1)
    {
      if doorTicks == 1 {
        // Таймер досяг нуля → двері автоматично зачиняються
        door      := Closed;
        doorTicks := 0;
      } else {
        // Продовжуємо відлік
        doorTicks := doorTicks - 1;
      }
    }


    // ====================================================================
    // 11) ОБСЛУГОВУВАННЯ ПОВЕРХУ
    //
    //    ServeHere: виконуємо всі запити на поточному поверсі.
    //    Викликається при відкритих дверях після OpenDoor().
    //
    //    Семантика: "пасажири входять/виходять на поверсі floor".
    //    Після ServeHere: floor більше не є у жодній з множин запитів.
    //
    //    Postcondition:
    //      Requests() == old(Requests()) - {floor}
    //    Тобто множина запитів зменшується рівно на поточний поверх.
    // ====================================================================

    method ServeHere()
      requires Valid()
      requires door == Open   // можна обслуговувати лише при відкритих дверях
      modifies this
      ensures Valid()
      ensures Requests()  == old(Requests()) - {floor}  // запит знято
      ensures plan        == RemoveFromPlan(old(plan), floor)
      ensures floor == old(floor) && dir  == old(dir)
      ensures door  == old(door)  && mode == old(mode)
      ensures doorTicks == old(doorTicks)
    {
      // Леми ПЕРЕД мутацією (пояснюють Z3 результат видалення)
      RemoveFromPlanSpec(plan, floor);     // SeqToSet після RemoveFromPlan
      RemovePreservesNoDups(plan, floor);  // NoDups зберігається після видалення

      // Видаляємо floor з усіх трьох множин запитів.
      // Якщо floor відсутній у якійсь множині — операція A - {x} нічого не змінює.
      cabin    := cabin    - {floor};
      hallUp   := hallUp   - {floor};
      hallDown := hallDown - {floor};

      // Видаляємо floor з упорядкованого плану
      plan := RemoveFromPlan(plan, floor);

      // Доказ для верифікатора: SeqToSet нового плану = нові Requests
      assert SeqToSet(plan) == Requests();
    }


    // ====================================================================
    // 12) РУХ КАБІНИ
    //
    //    Атомарний рух на один поверх вгору або вниз.
    //    ВИМОГИ:
    //      – mode == Normal     (аварійний режим забороняє рух)
    //      – door == Closed     (двері мають бути закриті)
    //      – floor < maxFloor   (є куди їхати вгору)
    //      – floor > minFloor   (є куди їхати вниз)
    // ====================================================================

    method MoveOneUp()
      requires Valid()
      requires mode == Normal && door == Closed && floor < maxFloor
      modifies this
      ensures Valid()
      ensures floor == old(floor) + 1  // поверх зріс на 1
      ensures dir == Up && door == Closed && doorTicks == 0
      ensures cabin == old(cabin) && hallUp == old(hallUp) && hallDown == old(hallDown)
      ensures plan  == old(plan)
    {
      dir   := Up;          // встановлюємо напрямок
      floor := floor + 1;   // переміщаємось вгору
      doorTicks := 0;       // двері залишаються Closed, таймер == 0
    }

    method MoveOneDown()
      requires Valid()
      requires mode == Normal && door == Closed && floor > minFloor
      modifies this
      ensures Valid()
      ensures floor + 1 == old(floor)  // поверх зменшився на 1
      ensures dir == Down && door == Closed && doorTicks == 0
      ensures cabin == old(cabin) && hallUp == old(hallUp) && hallDown == old(hallDown)
      ensures plan  == old(plan)
    {
      dir   := Down;        // встановлюємо напрямок
      floor := floor - 1;   // переміщаємось вниз
      doorTicks := 0;
    }

    // Stop: зупиняємо кабіну (переводимо dir у Idle).
    // Виклик у 3 випадках: аварія, відсутність запитів, або ліфт вже на потрібному поверсі.
    method Stop()
      requires Valid()
      modifies this
      ensures Valid()
      ensures dir == Idle
      ensures floor    == old(floor)    && door == old(door)  && mode == old(mode)
      ensures cabin    == old(cabin)    && hallUp  == old(hallUp)
      ensures hallDown == old(hallDown) && plan    == old(plan)
      ensures doorTicks == old(doorTicks)
    {
      dir := Idle;  // лише зміна напрямку; все інше залишається
    }


    // ====================================================================
    // 13) ДЕТЕРМІНОВАНИЙ КРОК КЕРУВАННЯ — "Мозок ліфта"
    //
    //    DeterministicStep() — головний контролер.
    //    Кожен "тік" системи викликає цей метод ОДИН раз.
    //    Метод обирає одну дію з фіксованими пріоритетами:
    //
    //    ПРІОРИТЕТИ (від найвищого до найнижчого):
    //    ┌──────┬─────────────────────────────────────────────────────┐
    //    │ 1.   │ Emergency → Stop() (безпека понад усе)              │
    //    │ 2.   │ door==Open → DoorTick() (обробляємо таймер дверей)  │
    //    │ 3.   │ RequestedHere → OpenDoor() + ServeHere()            │
    //    │ 4.   │ !HasRequests → Stop() (нема куди їхати)             │
    //    │ 5.   │ Є запити → MoveOneUp/Down до NearestRequest         │
    //    └──────┴─────────────────────────────────────────────────────┘
    //
    //    КЛЮЧОВА POSTCONDITION БЕЗПЕКИ:
    //    Якщо в попередньому стані: mode==Normal, door==Closed, і на
    //    поточному поверсі є запит → після кроку той запит ЗНЯТИЙ.
    //    (Умова old(mode)==Normal важлива: в аварійному режимі запити
    //    не знімаються — система чекає на відновлення.)
    // ====================================================================

    method DeterministicStep()
      requires Valid()
      modifies this
      ensures Valid()
      // Гарантія безпеки: запит на поточному поверсі завжди обробляється
      // при штатному режимі і закритих дверях.
      ensures old(mode) == Normal && old(door) == Closed && old(RequestedHere()) ==>
                !(floor in Requests())
    {
      // ── Крок 1: Аварійний режим → зупинка ─────────────────────────
      // Пріоритет 1: безпека понад усе. Ніяких інших дій.
      if mode == Emergency { Stop(); return; }

      // ── Крок 2: Двері відкриті → тікаємо таймер ───────────────────
      // Якщо двері відкриті: ми або чекаємо на пасажирів, або закриваємо.
      // DoorTick() зменшить таймер; якщо тікнув до 0 → закриє двері.
      // Після цього dir := Idle (кабіна не рухається поки двері відчинені).
      if door == Open { DoorTick(); dir := Idle; return; }

      // Інваріант тут: door == Closed (перевірки 1 і 2 пройдені)

      // ── Крок 3: Є запит на поточному поверсі → обслуговуємо ────────
      if RequestedHere() {
        // ghost-змінна: запам'ятовуємо поверх до мутацій для postcondition.
        // "ghost" означає: існує лише для верифікації, не компілюється.
        ghost var f := floor;
        assert f in Requests();  // підказка Z3: floor ∈ Requests() зараз

        dir := Idle;    // зупиняємось (на всяк випадок)
        OpenDoor();     // відчиняємо двері (dir==Idle — вимога OpenDoor)
        // Після OpenDoor: door==Open, doorTicks==maxDoorTicks,
        //                 Requests() НЕ змінились → f ще в Requests().
        assert f in Requests();

        ServeHere();    // знімаємо всі запити на поверсі floor
        // Після ServeHere: f ∉ Requests().
        assert !(f in Requests());
        return;
      }

      // ── Крок 4: Немає жодних запитів → зупиняємось ─────────────────
      if !HasRequests() { Stop(); return; }

      // ── Крок 5: Є запити деінде → рухаємось до найближчого ─────────
      // Доводимо |plan| > 0, щоб NearestInSeq можна було викликати.
      // (Якби plan == [] → SeqToSet(plan) == {} == Requests() → HasRequests()==false,
      //  але ми щойно перевірили HasRequests()==true — протиріччя!)
      assert |plan| > 0 by {
        if |plan| == 0 {
          assert SeqToSet(plan) == {};
          assert Requests() == {};
          // Суперечить HasRequests() == true
        }
      }

      // Виклик лем перед NearestRequest():
      //   – NearestInSeqMember: результат є елементом plan (і Requests())
      //   – NearestInSeqIsMin:  результат справді найближчий за Dist()
      NearestInSeqMember(plan, floor);
      NearestInSeqIsMin(plan, floor);

      var t := NearestRequest();  // найближчий поверх із запитом

      // Рухаємось у потрібному напрямку або зупиняємось якщо вже там
      if      t > floor { MoveOneUp();   }   // цільовий поверх вище → вгору
      else if t < floor { MoveOneDown(); }   // цільовий поверх нижче → вниз
      else              { Stop();        }   // ми вже на цільовому поверсі (можливо після ServeHere раніше)
    }
  }


  // 14) ДЕМОНСТРАЦІЙНИЙ СЦЕНАРІЙ (dafny run)

  method Main()
  {
    var e := new Elevator(0, 10, 0, 3);

    e.AddCabinCall(5);
    e.AddHallCall(3, HallDown);
    e.AddHallCall(7, HallUp);

    print "=== Старт: поверх ", e.floor, " ===\n";
    print "Запити в плані: ", |e.plan|, " поверхів\n\n";

    var i := 0;
    while i < 50
      invariant e.Valid()
      decreases 50 - i
    {
      e.DeterministicStep();

      print "Крок ", i + 1, ": ";
      print "поверх=", e.floor, "  ";
      print "напрям=", e.dir, "  ";
      print "двері=", e.door, "  ";
      print "запитів=", |e.plan|, "\n";

      i := i + 1;
    }

    print "\n=== Тест аварійного режиму ===\n";
    e.SetEmergency(true);
    print "mode=", e.mode, "  dir=", e.dir, "\n";
  }
}
