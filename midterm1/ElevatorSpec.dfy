// ФОРМАЛЬНА СПЕЦИФІКАЦІЯ ПРОГРАМНОЇ СИСТЕМИ "ЛІФТ" У DAFNY

module ElevatorValidPlus {

  // --------------------------------------------------------------------
  // 1) ПЕРЕЛІЧУВАНІ ТИПИ
  // --------------------------------------------------------------------

  datatype Direction = Up | Down | Idle
  datatype DoorState = Open | Closed
  datatype HallDir   = HallUp | HallDown
  datatype Mode      = Normal | Emergency


  // ====================================================================
  // 2) КЛАС Elevator
  // ====================================================================

  class Elevator {

    // ------------------------------------------------------------------
    // 2.1) Константи системи
    // ------------------------------------------------------------------
    const minFloor:     nat   // нижній поверх
    const maxFloor:     nat   // верхній поверх
    const maxDoorTicks: nat   // максимальний таймер дверей

    // ------------------------------------------------------------------
    // 2.2) Змінні стану
    // ------------------------------------------------------------------
    var floor:     nat
    var dir:       Direction
    var door:      DoorState
    var mode:      Mode

    var cabin:    set<nat>   // запити з кабіни
    var hallUp:   set<nat>   // виклики "вгору" з поверху
    var hallDown: set<nat>   // виклики "вниз" з поверху

    var doorTicks: nat       // таймер: 0=Closed, 1..maxDoorTicks=Open
    var plan:      seq<nat>  // черга обслуговування (без дублікатів)


    // ------------------------------------------------------------------
    // 3) ПЕРЕТВОРЕННЯ seq<nat> → set<nat>
    //    Використовує обмежений індексний comprehension:
    //    Dafny статично бачить скінченність (індекс < |s|).
    // ------------------------------------------------------------------

    function SeqToSet(s: seq<nat>): set<nat>
    {
      set i | 0 <= i < |s| :: s[i]
    }


    // ------------------------------------------------------------------
    // 4) ЛЕМИ ПРО SeqToSet
    //
    //    SMT-вирішувач Z3 не завжди автоматично виводить зв'язки між
    //    seq та set. Леми — це "підказки": ми доводимо факти вручну,
    //    а потім викликаємо лему перед тим кодом, де вона потрібна.
    // ------------------------------------------------------------------

    // SeqToSet(s + [x]) == SeqToSet(s) + {x}
    // Доводиться двосторонньою включеністю (⊆ в обох напрямках).
    lemma SeqToSetAppend(s: seq<nat>, x: nat)
      ensures SeqToSet(s + [x]) == SeqToSet(s) + {x}
    {
      // Напрям →: кожен e з SeqToSet(s+[x]) є або в SeqToSet(s), або == x
      forall e | e in SeqToSet(s + [x])
        ensures e in SeqToSet(s) + {x}
      {
        var i :| 0 <= i < |s + [x]| && (s + [x])[i] == e;
        if i < |s| { assert s[i] == e; }
        else        { assert e == x;   }
      }
      // Напрям ←: кожен e з SeqToSet(s)+{x} є в SeqToSet(s+[x])
      forall e | e in SeqToSet(s) + {x}
        ensures e in SeqToSet(s + [x])
      {
        if e in SeqToSet(s) {
          var i :| 0 <= i < |s| && s[i] == e;
          assert (s + [x])[i] == e;
        } else {
          // e == x, знаходиться на позиції |s|
          assert (s + [x])[|s|] == x;
        }
      }
    }

    // SeqToSet([h] + t) == {h} + SeqToSet(t)
    lemma SeqToSetCons(h: nat, t: seq<nat>)
      ensures SeqToSet([h] + t) == {h} + SeqToSet(t)
    {
      forall e | e in SeqToSet([h] + t)
        ensures e in {h} + SeqToSet(t)
      {
        var i :| 0 <= i < |[h] + t| && ([h] + t)[i] == e;
        if i == 0 { assert e == h; }
        else      { assert t[i-1] == e; }
      }
      forall e | e in {h} + SeqToSet(t)
        ensures e in SeqToSet([h] + t)
      {
        if e == h { assert ([h] + t)[0] == h; }
        else {
          var i :| 0 <= i < |t| && t[i] == e;
          assert ([h] + t)[i + 1] == e;
        }
      }
    }

    // AddToPlan(s, x): якщо x ∈ s — повертає s без змін;
    //                  якщо x ∉ s — SeqToSet зростає на {x}
    lemma AddToPlanSpec(s: seq<nat>, x: nat)
      ensures x in SeqToSet(s) ==>
                SeqToSet(AddToPlan(s, x)) == SeqToSet(s)
      ensures x !in SeqToSet(s) ==>
                SeqToSet(AddToPlan(s, x)) == SeqToSet(s) + {x}
    {
      if x in SeqToSet(s) {
        assert AddToPlan(s, x) == s;
      } else {
        assert AddToPlan(s, x) == s + [x];
        SeqToSetAppend(s, x);
      }
    }

    // SeqToSet(RemoveFromPlan(s, x)) == SeqToSet(s) - {x}
    // за умови NoDups(s) (унікальність гарантує коректне видалення)
    lemma RemoveFromPlanSpec(s: seq<nat>, x: nat)
      requires NoDups(s)
      ensures  SeqToSet(RemoveFromPlan(s, x)) == SeqToSet(s) - {x}
    {
      if |s| == 0 {
        // Порожньо — тривіально: {} == {} - {x}
      } else if s[0] == x {
        // Видалили голову: залишився s[1..]
        forall e | e in SeqToSet(s[1..])
          ensures e in SeqToSet(s) - {x}
        {
          var i :| 0 <= i < |s[1..]| && s[1..][i] == e;
          assert s[i + 1] == e;
          // e != x бо NoDups: s[0]==x і s[i+1] мали б дублюватись
          assert e != x by {
            if e == x { assert s[0] == s[i + 1]; }
          }
        }
        forall e | e in SeqToSet(s) - {x}
          ensures e in SeqToSet(s[1..])
        {
          var i :| 0 <= i < |s| && s[i] == e;
          assert i != 0 by { assert s[0] == x && e != x; }
          assert s[1..][i - 1] == e;
        }
      } else {
        // Голова != x: рекурсія на хвіст
        RemoveFromPlanSpec(s[1..], x);
        var r := RemoveFromPlan(s[1..], x);
        // RemoveFromPlan(s, x) == [s[0]] + r
        SeqToSetCons(s[0], r);
        SeqToSetCons(s[0], s[1..]);
        // SeqToSet([s[0]]+r) == {s[0]} + SeqToSet(r)
        //                     == {s[0]} + SeqToSet(s[1..]) - {x}
        //                     == SeqToSet(s) - {x}   (бо s[0] != x)
      }
    }

    // NoDups зберігається після RemoveFromPlan
    lemma RemovePreservesNoDups(s: seq<nat>, x: nat)
      requires NoDups(s)
      ensures  NoDups(RemoveFromPlan(s, x))
    {
      if |s| == 0 {
      } else if s[0] == x {
        // Залишився s[1..]: він теж NoDups (підпослідовність)
        assert NoDups(s[1..]) by {
          forall i, j | 0 <= i < |s[1..]| && 0 <= j < |s[1..]| && i != j
            ensures s[1..][i] != s[1..][j]
          { assert s[i+1] != s[j+1]; }
        }
      } else {
        RemovePreservesNoDups(s[1..], x);
        var r := RemoveFromPlan(s[1..], x);
        // Треба NoDups([s[0]] + r)
        RemoveFromPlanSpec(s[1..], x);
        // SeqToSet(r) ⊆ SeqToSet(s[1..])
        // s[0] !in SeqToSet(s[1..]) (NoDups s і s[0] є лише на позиції 0)
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
              assert ([s[0]] + r)[j] == r[j-1];
              assert r[j-1] in SeqToSet(r);
              assert r[j-1] in SeqToSet(s[1..]);
            } else if j == 0 {
              assert ([s[0]] + r)[i] == r[i-1];
              assert r[i-1] in SeqToSet(r);
              assert r[i-1] in SeqToSet(s[1..]);
            } else {
              assert r[i-1] != r[j-1];
            }
          }
        }
      }
    }

    // NoDups зберігається після AddToPlan
    lemma AddToPlanPreservesNoDups(s: seq<nat>, x: nat)
      requires NoDups(s)
      ensures  NoDups(AddToPlan(s, x))
    {
      if x in SeqToSet(s) {
        assert AddToPlan(s, x) == s;
      } else {
        assert AddToPlan(s, x) == s + [x];
        assert NoDups(s + [x]) by {
          forall i, j | 0 <= i < |s + [x]|
                     && 0 <= j < |s + [x]| && i != j
            ensures (s + [x])[i] != (s + [x])[j]
          {
            if i < |s| && j < |s| {
              assert s[i] != s[j];
            } else if i == |s| {
              // (s+[x])[i] == x, (s+[x])[j] == s[j]
              assert (s + [x])[i] == x;
              assert (s + [x])[j] == s[j];
              assert s[j] != x by { assert x !in SeqToSet(s); }
            } else {
              assert (s + [x])[j] == x;
              assert (s + [x])[i] == s[i];
              assert s[i] != x by { assert x !in SeqToSet(s); }
            }
          }
        }
      }
    }

    // InRange зберігається після AddToPlan
    lemma AddToPlanInRange(s: seq<nat>, x: nat, minF: nat, maxF: nat)
      requires forall i :: 0 <= i < |s| ==> minF <= s[i] <= maxF
      requires minF <= x <= maxF
      ensures  forall i :: 0 <= i < |AddToPlan(s, x)| ==>
                             minF <= AddToPlan(s, x)[i] <= maxF
    {
      if x in SeqToSet(s) { assert AddToPlan(s, x) == s; }
      else                 { assert AddToPlan(s, x) == s + [x]; }
    }


    // ------------------------------------------------------------------
    // 5) ОСНОВНІ ДОПОМІЖНІ ФУНКЦІЇ ТА ПРЕДИКАТИ
    // ------------------------------------------------------------------

    predicate InRange(f: nat)
      reads this
    { minFloor <= f <= maxFloor }

    function Requests(): set<nat>
      reads this
    { cabin + hallUp + hallDown }

    function HasRequests(): bool
      reads this
    { Requests() != {} }

    function RequestedHere(): bool
      reads this
    { floor in Requests() }

    function Dist(a: nat, b: nat): nat
    { if a <= b then b - a else a - b }

    // ---- NearestRequest ----
    // ":| " вимагає від Dafny довести існування і
    // однозначність. Замість цього використовуємо явний алгоритм
    // NearestInSeq, який ітерує по плану і повертає мінімум.

    // Рекурсивний пошук найближчого елемента у послідовності
    function NearestInSeq(s: seq<nat>, target: nat): nat
      requires |s| > 0
    {
      if |s| == 1 then s[0]
      else
        var rest := NearestInSeq(s[1..], target);
        if Dist(target, s[0]) <= Dist(target, rest) then s[0] else rest
    }

    // Лема: результат NearestInSeq є елементом s
    lemma NearestInSeqMember(s: seq<nat>, target: nat)
      requires |s| > 0
      ensures  NearestInSeq(s, target) in SeqToSet(s)
    {
      if |s| == 1 {
        assert s[0] in SeqToSet(s);
      } else {
        NearestInSeqMember(s[1..], target);
        var rest := NearestInSeq(s[1..], target);
        if Dist(target, s[0]) <= Dist(target, rest) {
          assert s[0] in SeqToSet(s);
        } else {
          // rest ∈ SeqToSet(s[1..]) ⊆ SeqToSet(s)
          forall e | e in SeqToSet(s[1..]) ensures e in SeqToSet(s) {
            var i :| 0 <= i < |s[1..]| && s[1..][i] == e;
            assert s[i+1] == e;
          }
        }
      }
    }

    // Лема: NearestInSeq повертає елемент з мінімальною відстанню
    lemma NearestInSeqIsMin(s: seq<nat>, target: nat)
      requires |s| > 0
      ensures  forall q :: q in SeqToSet(s) ==>
                 Dist(target, NearestInSeq(s, target)) <= Dist(target, q)
    {
      if |s| == 1 {
        // єдиний елемент — тривіально мінімальний
      } else {
        NearestInSeqIsMin(s[1..], target);
        var rest   := NearestInSeq(s[1..], target);
        var chosen := NearestInSeq(s, target);
        forall q | q in SeqToSet(s)
          ensures Dist(target, chosen) <= Dist(target, q)
        {
          if q == s[0] {
            // chosen == s[0] або chosen == rest ≤ s[0] за відстанню
          } else {
            // q ∈ SeqToSet(s[1..])
            var i :| 0 <= i < |s| && s[i] == q;
            assert i > 0;
            assert s[1..][i-1] == q;
            // За IH: Dist(target, rest) <= Dist(target, q)
            // chosen <= rest (за визначенням NearestInSeq)
          }
        }
      }
    }

    function NearestRequest(): nat
      requires Valid()
      requires HasRequests()
      reads this
    {
      // |plan| > 0 гарантовано: SeqToSet(plan)==Requests() і Requests()!={}
      NearestInSeq(plan, floor)
    }

    function DistToNearest(): nat
      requires Valid()
      reads this
    {
      if HasRequests() then Dist(floor, NearestRequest()) else 0
    }

    predicate NoDups(s: seq<nat>)
    {
      forall i, j ::
        0 <= i < |s| && 0 <= j < |s| && i != j ==> s[i] != s[j]
    }

    function RemoveFromPlan(s: seq<nat>, x: nat): seq<nat>
    {
      if |s| == 0 then []
      else if s[0] == x then s[1..]
      else [s[0]] + RemoveFromPlan(s[1..], x)
    }

    function AddToPlan(s: seq<nat>, x: nat): seq<nat>
    {
      if x in SeqToSet(s) then s else s + [x]
    }


    // ------------------------------------------------------------------
    // 6) ГЛОБАЛЬНИЙ ІНВАРІАНТ Valid()
    // ------------------------------------------------------------------

    predicate Valid()
      reads this
    {
      minFloor <= maxFloor
      && maxDoorTicks >= 1
      && InRange(floor)

      && (forall f :: f in cabin    ==> InRange(f))
      && (forall f :: f in hallUp   ==> InRange(f))
      && (forall f :: f in hallDown ==> InRange(f))

      && (forall f :: f in hallUp   ==> f < maxFloor)
      && (forall f :: f in hallDown ==> f > minFloor)

      // Безпека руху: двері та рух взаємовиключні
      && (door == Open ==> dir == Idle)
      && ((dir == Up || dir == Down) ==> door == Closed)

      // Аварійний режим: рух заборонений
      && (mode == Emergency ==> dir == Idle)

      // Узгодженість таймера дверей
      && (door == Closed ==> doorTicks == 0)
      && (door == Open   ==> 1 <= doorTicks <= maxDoorTicks)

      // Коректність плану
      && (forall i :: 0 <= i < |plan| ==> InRange(plan[i]))
      && NoDups(plan)
      && SeqToSet(plan) == Requests()
    }


    // ------------------------------------------------------------------
    // 7) КОНСТРУКТОР
    // ------------------------------------------------------------------

    constructor(minF: nat, maxF: nat, start: nat, maxTicks: nat)
      requires minF <= maxF
      requires minF <= start <= maxF
      requires maxTicks >= 1
      ensures Valid()
      ensures minFloor == minF && maxFloor == maxF && maxDoorTicks == maxTicks
      ensures floor == start
      ensures dir == Idle && door == Closed && mode == Normal
      ensures cabin == {} && hallUp == {} && hallDown == {}
      ensures doorTicks == 0 && plan == []
    {
      minFloor     := minF;
      maxFloor     := maxF;
      maxDoorTicks := maxTicks;
      floor        := start;
      dir          := Idle;
      door         := Closed;
      mode         := Normal;
      cabin        := {};
      hallUp       := {};
      hallDown     := {};
      doorTicks    := 0;
      plan         := [];
    }


    // ------------------------------------------------------------------
    // 8) РЕЄСТРАЦІЯ ЗАПИТІВ
    // ------------------------------------------------------------------

    // Запит із кабіни: пасажир натиснув кнопку поверху f всередині ліфта
    method AddCabinCall(f: nat)
      requires Valid()
      requires InRange(f)
      modifies this
      ensures Valid()
      ensures cabin     == old(cabin) + {f}
      ensures hallUp    == old(hallUp) && hallDown == old(hallDown)
      ensures plan      == AddToPlan(old(plan), f)
      ensures floor     == old(floor)  && dir  == old(dir)
      ensures door      == old(door)   && mode == old(mode)
      ensures doorTicks == old(doorTicks)
    {
      // Виклики лем ПЕРЕД мутацією: посилаються на поточний стан plan
      AddToPlanSpec(plan, f);
      AddToPlanPreservesNoDups(plan, f);
      AddToPlanInRange(plan, f, minFloor, maxFloor);

      // Обчислюємо новий plan ДО зміни cabin, щоб уникнути ghost-змінних.
      // AddToPlan — чиста функція, тож її можна викликати у виконуваному коді.
      var newPlan := AddToPlan(plan, f);  // НЕ ghost: використовується в присвоєнні
      cabin := cabin + {f};
      plan  := newPlan;

      assert SeqToSet(plan) == Requests();
    }

    // Виклик із поверхового майданчика: пасажир хоче їхати у напрямку d
    method AddHallCall(f: nat, d: HallDir)
      requires Valid()
      requires InRange(f)
      requires d == HallUp   ==> f < maxFloor
      requires d == HallDown ==> f > minFloor
      modifies this
      ensures Valid()
      ensures cabin     == old(cabin)
      ensures plan      == AddToPlan(old(plan), f)
      ensures floor     == old(floor) && dir  == old(dir)
      ensures door      == old(door)  && mode == old(mode)
      ensures doorTicks == old(doorTicks)
      // кожен ensures окремий рядок із &&
      ensures (d == HallUp ==>
                 hallUp   == old(hallUp) + {f} &&
                 hallDown == old(hallDown))
      ensures (d == HallDown ==>
                 hallDown == old(hallDown) + {f} &&
                 hallUp   == old(hallUp))
    {
      AddToPlanSpec(plan, f);
      AddToPlanPreservesNoDups(plan, f);
      AddToPlanInRange(plan, f, minFloor, maxFloor);

      // Обчислюємо новий план ДО мутації hall-множин
      var newPlan := AddToPlan(plan, f);

      if d == HallUp {
        hallUp := hallUp + {f};
      } else {
        hallDown := hallDown + {f};
      }
      plan := newPlan;

      assert SeqToSet(plan) == Requests();
    }


    // ------------------------------------------------------------------
    // 9) АВАРІЙНИЙ РЕЖИМ
    // ------------------------------------------------------------------

    method SetEmergency(on: bool)
      requires Valid()
      modifies this
      ensures Valid()
      ensures (on  ==> mode == Emergency && dir == Idle)
      ensures (!on ==> mode == Normal)
      ensures floor     == old(floor)    && door == old(door)
      ensures cabin     == old(cabin)    && hallUp  == old(hallUp)
      ensures hallDown  == old(hallDown) && doorTicks == old(doorTicks)
      ensures plan == old(plan)
    {
      if on { mode := Emergency; dir := Idle; }
      else  { mode := Normal; }
    }


    // ------------------------------------------------------------------
    // 10) КЕРУВАННЯ ДВЕРИМА
    // ------------------------------------------------------------------

    method OpenDoor()
      requires Valid()
      requires dir == Idle
      modifies this
      ensures Valid()
      ensures door      == Open
      ensures doorTicks == maxDoorTicks
      ensures floor == old(floor) && dir  == old(dir)  && mode == old(mode)
      ensures cabin == old(cabin) && hallUp == old(hallUp) && hallDown == old(hallDown)
      ensures plan  == old(plan)
    {
      door      := Open;
      doorTicks := maxDoorTicks;
    }

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

    method DoorTick()
      requires Valid()
      requires door == Open
      modifies this
      ensures Valid()
      ensures cabin    == old(cabin)    && hallUp  == old(hallUp)
      ensures hallDown == old(hallDown) && plan    == old(plan)
      ensures floor == old(floor) && dir == old(dir) && mode == old(mode)
      ensures (old(doorTicks) == 1 ==> door == Closed && doorTicks == 0)
      ensures (old(doorTicks) >  1 ==> door == Open   && doorTicks == old(doorTicks) - 1)
    {
      if doorTicks == 1 { door := Closed; doorTicks := 0; }
      else              { doorTicks := doorTicks - 1;     }
    }


    // ------------------------------------------------------------------
    // 11) ОБСЛУГОВУВАННЯ ПОВЕРХУ
    // ------------------------------------------------------------------

    method ServeHere()
      requires Valid()
      requires door == Open
      modifies this
      ensures Valid()
      ensures Requests()  == old(Requests()) - {floor}
      ensures plan        == RemoveFromPlan(old(plan), floor)
      ensures floor == old(floor) && dir  == old(dir)
      ensures door  == old(door)  && mode == old(mode)
      ensures doorTicks == old(doorTicks)
    {
      // Леми ПЕРЕД мутацією
      RemoveFromPlanSpec(plan, floor);    // SeqToSet після видалення
      RemovePreservesNoDups(plan, floor); // NoDups зберігається

      cabin    := cabin    - {floor};
      hallUp   := hallUp   - {floor};
      hallDown := hallDown - {floor};
      plan     := RemoveFromPlan(plan, floor);

      // SeqToSet(plan) = SeqToSet(old_plan) - {floor}
      //                = old_Requests - {floor}
      //                = new_Requests
      assert SeqToSet(plan) == Requests();
    }


    // ------------------------------------------------------------------
    // 12) РУХ КАБІНИ
    // ------------------------------------------------------------------

    method MoveOneUp()
      requires Valid()
      requires mode == Normal && door == Closed && floor < maxFloor
      modifies this
      ensures Valid()
      ensures floor == old(floor) + 1
      ensures dir == Up && door == Closed && doorTicks == 0
      ensures cabin == old(cabin) && hallUp == old(hallUp) && hallDown == old(hallDown)
      ensures plan  == old(plan)
    {
      dir := Up; floor := floor + 1; doorTicks := 0;
    }

    method MoveOneDown()
      requires Valid()
      requires mode == Normal && door == Closed && floor > minFloor
      modifies this
      ensures Valid()
      ensures floor + 1 == old(floor)
      ensures dir == Down && door == Closed && doorTicks == 0
      ensures cabin == old(cabin) && hallUp == old(hallUp) && hallDown == old(hallDown)
      ensures plan  == old(plan)
    {
      dir := Down; floor := floor - 1; doorTicks := 0;
    }

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
      dir := Idle;
    }


    // ------------------------------------------------------------------
    // 13) ДЕТЕРМІНОВАНИЙ КРОК КЕРУВАННЯ
    //
    //     Пріоритети (від вищого до нижчого):
    //       1. Emergency  => зупинка
    //       2. door==Open => DoorTick (чекаємо закриття)
    //       3. RequestedHere => OpenDoor + ServeHere
    //       4. !HasRequests  => Stop
    //       5. Є запити деінде => рух до NearestRequest
    // ------------------------------------------------------------------

    method DeterministicStep()
      requires Valid()
      modifies this
      ensures Valid()
      // Ключова безпека: якщо двері були зачинені, режим штатний і є запит тут —
      // після кроку цей запит буде ЗНЯТИЙ.
      // Умова old(mode)==Normal необхідна: в аварійному режимі ліфт лише
      // зупиняється, запити НЕ знімаються (система чекає відновлення).
      ensures old(mode) == Normal && old(door) == Closed && old(RequestedHere()) ==>
                !(floor in Requests())
    {
      // --- 1. Аварійний режим ---
      if mode == Emergency { Stop(); return; }

      // --- 2. Двері відкриті: обробляємо таймер ---
      if door == Open { DoorTick(); dir := Idle; return; }

      // Тут: door == Closed

      // --- 3. Запит на поточному поверсі ---
      if RequestedHere() {
        // ghost-змінна: фіксуємо поверх ДО мутацій для postcondition
        ghost var f := floor;
        assert f in Requests();   // підказка: floor in Requests()

        dir := Idle;
        OpenDoor();
        // OpenDoor не змінює Requests: floor все ще in Requests()
        assert f in Requests();
        ServeHere();
        // ServeHere видаляє f: тепер f !in Requests()
        assert !(f in Requests());
        return;
      }

      // --- 4. Немає жодних запитів ---
      if !HasRequests() { Stop(); return; }

      // --- 5. Рухаємося до найближчого запиту ---
      // Доводимо |plan| > 0 (потрібно для NearestInSeq)
      assert |plan| > 0 by {
        // Якби plan був порожній:
        //   SeqToSet([]) == {} == Requests() => HasRequests() == false
        // Але ми щойно перевірили HasRequests() == true — протиріччя.
        if |plan| == 0 {
          assert SeqToSet(plan) == {};
          assert Requests() == {};
        }
      }

      // Виклик лем для NearestRequest, щоб вериф'ятор знав:
      NearestInSeqMember(plan, floor);  // результат є в SeqToSet(plan)
      NearestInSeqIsMin(plan, floor);   // результат мінімальний за відстанню

      var t := NearestRequest();

      if      t > floor { MoveOneUp();   }
      else if t < floor { MoveOneDown(); }
      else              { Stop();        }
    }
  }


  // ====================================================================
  // 14) ДЕМОНСТРАЦІЙНИЙ СЦЕНАРІЙ (dafny run)
  // ====================================================================

  method Main()
  {
    // Ліфт: поверхи 0..10, старт на 0-му, таймер дверей = 3 тіки
    var e := new Elevator(0, 10, 0, 3);
    assert e.Valid();

    // Реєстрація запитів:
    //   кабіна: поверх 5
    //   поверх 3: кнопка "вниз"
    //   поверх 7: кнопка "вгору"
    e.AddCabinCall(5);
    e.AddHallCall(3, HallDown);
    e.AddHallCall(7, HallUp);
    assert e.Valid();

    // Симуляція 50 кроків
    var i := 0;
    while i < 50
      invariant e.Valid()
      decreases 50 - i
    {
      e.DeterministicStep();
      // Перевірка ключової властивості безпеки на кожному кроці:
      // відкриті двері => кабіна нерухома
      assert e.door == Open ==> e.dir == Idle;
      i := i + 1;
    }

    // Тест аварійного режиму
    e.SetEmergency(true);
    assert e.Valid();
    assert e.mode == Emergency;
    assert e.dir  == Idle;
  }
}
