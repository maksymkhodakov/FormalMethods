import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_

# Module: ElevatorValidPlus

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Main(noArgsParameter__):
        d_0_e_: Elevator
        nw0_ = Elevator()
        nw0_.ctor__(0, 10, 0, 3)
        d_0_e_ = nw0_
        (d_0_e_).AddCabinCall(5)
        (d_0_e_).AddHallCall(3, HallDir_HallDown())
        (d_0_e_).AddHallCall(7, HallDir_HallUp())
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "=== Старт: поверх "))).VerbatimString(False))
        _dafny.print(_dafny.string_of(d_0_e_.floor))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ===\n"))).VerbatimString(False))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Запити в плані: "))).VerbatimString(False))
        _dafny.print(_dafny.string_of(len(d_0_e_.plan)))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " поверхів\n\n"))).VerbatimString(False))
        d_1_i_: int
        d_1_i_ = 0
        while (d_1_i_) < (50):
            (d_0_e_).DeterministicStep()
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Крок "))).VerbatimString(False))
            _dafny.print(_dafny.string_of((d_1_i_) + (1)))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ": "))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "поверх="))).VerbatimString(False))
            _dafny.print(_dafny.string_of(d_0_e_.floor))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  "))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "напрям="))).VerbatimString(False))
            _dafny.print(_dafny.string_of(d_0_e_.dir_))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  "))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "двері="))).VerbatimString(False))
            _dafny.print(_dafny.string_of(d_0_e_.door))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  "))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "запитів="))).VerbatimString(False))
            _dafny.print(_dafny.string_of(len(d_0_e_.plan)))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
            d_1_i_ = (d_1_i_) + (1)
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n=== Тест аварійного режиму ===\n"))).VerbatimString(False))
        (d_0_e_).SetEmergency(True)
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "mode="))).VerbatimString(False))
        _dafny.print(_dafny.string_of(d_0_e_.mode))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "  dir="))).VerbatimString(False))
        _dafny.print(_dafny.string_of(d_0_e_.dir_))
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))


class Direction:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [Direction_Up(), Direction_Down(), Direction_Idle()]
    @classmethod
    def default(cls, ):
        return lambda: Direction_Up()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Up(self) -> bool:
        return isinstance(self, Direction_Up)
    @property
    def is_Down(self) -> bool:
        return isinstance(self, Direction_Down)
    @property
    def is_Idle(self) -> bool:
        return isinstance(self, Direction_Idle)

class Direction_Up(Direction, NamedTuple('Up', [])):
    def __dafnystr__(self) -> str:
        return f'ElevatorValidPlus.Direction.Up'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Direction_Up)
    def __hash__(self) -> int:
        return super().__hash__()

class Direction_Down(Direction, NamedTuple('Down', [])):
    def __dafnystr__(self) -> str:
        return f'ElevatorValidPlus.Direction.Down'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Direction_Down)
    def __hash__(self) -> int:
        return super().__hash__()

class Direction_Idle(Direction, NamedTuple('Idle', [])):
    def __dafnystr__(self) -> str:
        return f'ElevatorValidPlus.Direction.Idle'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Direction_Idle)
    def __hash__(self) -> int:
        return super().__hash__()


class DoorState:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [DoorState_Open(), DoorState_Closed()]
    @classmethod
    def default(cls, ):
        return lambda: DoorState_Open()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Open(self) -> bool:
        return isinstance(self, DoorState_Open)
    @property
    def is_Closed(self) -> bool:
        return isinstance(self, DoorState_Closed)

class DoorState_Open(DoorState, NamedTuple('Open', [])):
    def __dafnystr__(self) -> str:
        return f'ElevatorValidPlus.DoorState.Open'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, DoorState_Open)
    def __hash__(self) -> int:
        return super().__hash__()

class DoorState_Closed(DoorState, NamedTuple('Closed', [])):
    def __dafnystr__(self) -> str:
        return f'ElevatorValidPlus.DoorState.Closed'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, DoorState_Closed)
    def __hash__(self) -> int:
        return super().__hash__()


class HallDir:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [HallDir_HallUp(), HallDir_HallDown()]
    @classmethod
    def default(cls, ):
        return lambda: HallDir_HallUp()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_HallUp(self) -> bool:
        return isinstance(self, HallDir_HallUp)
    @property
    def is_HallDown(self) -> bool:
        return isinstance(self, HallDir_HallDown)

class HallDir_HallUp(HallDir, NamedTuple('HallUp', [])):
    def __dafnystr__(self) -> str:
        return f'ElevatorValidPlus.HallDir.HallUp'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, HallDir_HallUp)
    def __hash__(self) -> int:
        return super().__hash__()

class HallDir_HallDown(HallDir, NamedTuple('HallDown', [])):
    def __dafnystr__(self) -> str:
        return f'ElevatorValidPlus.HallDir.HallDown'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, HallDir_HallDown)
    def __hash__(self) -> int:
        return super().__hash__()


class Mode:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [Mode_Normal(), Mode_Emergency()]
    @classmethod
    def default(cls, ):
        return lambda: Mode_Normal()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Normal(self) -> bool:
        return isinstance(self, Mode_Normal)
    @property
    def is_Emergency(self) -> bool:
        return isinstance(self, Mode_Emergency)

class Mode_Normal(Mode, NamedTuple('Normal', [])):
    def __dafnystr__(self) -> str:
        return f'ElevatorValidPlus.Mode.Normal'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Mode_Normal)
    def __hash__(self) -> int:
        return super().__hash__()

class Mode_Emergency(Mode, NamedTuple('Emergency', [])):
    def __dafnystr__(self) -> str:
        return f'ElevatorValidPlus.Mode.Emergency'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Mode_Emergency)
    def __hash__(self) -> int:
        return super().__hash__()


class Elevator:
    def  __init__(self):
        self.floor: int = int(0)
        self.dir_: Direction = Direction.default()()
        self.door: DoorState = DoorState.default()()
        self.mode: Mode = Mode.default()()
        self.cabin: _dafny.Set = _dafny.Set({})
        self.hallUp: _dafny.Set = _dafny.Set({})
        self.hallDown: _dafny.Set = _dafny.Set({})
        self.doorTicks: int = int(0)
        self.plan: _dafny.Seq = _dafny.Seq({})
        self._minFloor: int = int(0)
        self._maxFloor: int = int(0)
        self._maxDoorTicks: int = int(0)
        pass

    def __dafnystr__(self) -> str:
        return "ElevatorValidPlus.Elevator"
    def SeqToSet(self, s):
        def iife0_():
            coll0_ = _dafny.Set()
            compr_0_: int
            for compr_0_ in _dafny.IntegerRange(0, len(s)):
                d_0_i_: int = compr_0_
                if ((0) <= (d_0_i_)) and ((d_0_i_) < (len(s))):
                    coll0_ = coll0_.union(_dafny.Set([(s)[d_0_i_]]))
            return _dafny.Set(coll0_)
        return iife0_()
        

    def InRange(self, f):
        return (((self).minFloor) <= (f)) and ((f) <= ((self).maxFloor))

    def Requests(self):
        return ((self.cabin) | (self.hallUp)) | (self.hallDown)

    def HasRequests(self):
        return ((self).Requests()) != (_dafny.Set({}))

    def RequestedHere(self):
        return (self.floor) in ((self).Requests())

    def Dist(self, a, b):
        if (a) <= (b):
            return (b) - (a)
        elif True:
            return (a) - (b)

    def NearestInSeq(self, s, target):
        if (len(s)) == (1):
            return (s)[0]
        elif True:
            d_0_rest_ = (self).NearestInSeq(_dafny.SeqWithoutIsStrInference((s)[1::]), target)
            if ((self).Dist(target, (s)[0])) <= ((self).Dist(target, d_0_rest_)):
                return (s)[0]
            elif True:
                return d_0_rest_

    def NearestRequest(self):
        return (self).NearestInSeq(self.plan, self.floor)

    def DistToNearest(self):
        if (self).HasRequests():
            return (self).Dist(self.floor, (self).NearestRequest())
        elif True:
            return 0

    def NoDups(self, s):
        def lambda0_(forall_var_0_):
            def lambda1_(forall_var_1_):
                d_1_j_: int = forall_var_1_
                return not (((((0) <= (d_0_i_)) and ((d_0_i_) < (len(s)))) and (((0) <= (d_1_j_)) and ((d_1_j_) < (len(s))))) and ((d_0_i_) != (d_1_j_))) or (((s)[d_0_i_]) != ((s)[d_1_j_]))

            d_0_i_: int = forall_var_0_
            return _dafny.quantifier(_dafny.IntegerRange(0, len(s)), True, lambda1_)

        return _dafny.quantifier(_dafny.IntegerRange(0, len(s)), True, lambda0_)

    def RemoveFromPlan(self, s, x):
        d_0___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif ((s)[0]) == (x):
                    return (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference((s)[1::]))
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference([(s)[0]]))
                    in0_ = _this
                    in1_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    in2_ = x
                    _this = in0_
                    
                    s = in1_
                    x = in2_
                    raise _dafny.TailCall()
                break

    def AddToPlan(self, s, x):
        if (x) in ((self).SeqToSet(s)):
            return s
        elif True:
            return (s) + (_dafny.SeqWithoutIsStrInference([x]))

    def Valid(self):
        def lambda0_(forall_var_0_):
            d_0_f_: int = forall_var_0_
            if System_.nat._Is(d_0_f_):
                return not ((d_0_f_) in (self.cabin)) or ((self).InRange(d_0_f_))
            elif True:
                return True

        def lambda1_(forall_var_1_):
            d_1_f_: int = forall_var_1_
            if System_.nat._Is(d_1_f_):
                return not ((d_1_f_) in (self.hallUp)) or ((self).InRange(d_1_f_))
            elif True:
                return True

        def lambda2_(forall_var_2_):
            d_2_f_: int = forall_var_2_
            if System_.nat._Is(d_2_f_):
                return not ((d_2_f_) in (self.hallDown)) or ((self).InRange(d_2_f_))
            elif True:
                return True

        def lambda3_(forall_var_3_):
            d_3_f_: int = forall_var_3_
            return not ((d_3_f_) in (self.hallUp)) or ((d_3_f_) < ((self).maxFloor))

        def lambda4_(forall_var_4_):
            d_4_f_: int = forall_var_4_
            return not ((d_4_f_) in (self.hallDown)) or ((d_4_f_) > ((self).minFloor))

        def lambda5_(forall_var_5_):
            d_5_i_: int = forall_var_5_
            return not (((0) <= (d_5_i_)) and ((d_5_i_) < (len(self.plan)))) or ((self).InRange((self.plan)[d_5_i_]))

        return (((((((((((((((((self).minFloor) <= ((self).maxFloor)) and (((self).maxDoorTicks) >= (1))) and ((self).InRange(self.floor))) and (_dafny.quantifier((self.cabin).Elements, True, lambda0_))) and (_dafny.quantifier((self.hallUp).Elements, True, lambda1_))) and (_dafny.quantifier((self.hallDown).Elements, True, lambda2_))) and (_dafny.quantifier((self.hallUp).Elements, True, lambda3_))) and (_dafny.quantifier((self.hallDown).Elements, True, lambda4_))) and (not ((self.door) == (DoorState_Open())) or ((self.dir_) == (Direction_Idle())))) and (not (((self.dir_) == (Direction_Up())) or ((self.dir_) == (Direction_Down()))) or ((self.door) == (DoorState_Closed())))) and (not ((self.mode) == (Mode_Emergency())) or ((self.dir_) == (Direction_Idle())))) and (not ((self.door) == (DoorState_Closed())) or ((self.doorTicks) == (0)))) and (not ((self.door) == (DoorState_Open())) or (((1) <= (self.doorTicks)) and ((self.doorTicks) <= ((self).maxDoorTicks))))) and (_dafny.quantifier(_dafny.IntegerRange(0, len(self.plan)), True, lambda5_))) and ((self).NoDups(self.plan))) and (((self).SeqToSet(self.plan)) == ((self).Requests()))

    def ctor__(self, minF, maxF, start, maxTicks):
        (self)._minFloor = minF
        (self)._maxFloor = maxF
        (self)._maxDoorTicks = maxTicks
        (self).floor = start
        (self).dir_ = Direction_Idle()
        (self).door = DoorState_Closed()
        (self).mode = Mode_Normal()
        (self).cabin = _dafny.Set({})
        (self).hallUp = _dafny.Set({})
        (self).hallDown = _dafny.Set({})
        (self).doorTicks = 0
        (self).plan = _dafny.SeqWithoutIsStrInference([])

    def AddCabinCall(self, f):
        d_0_newPlan_: _dafny.Seq
        d_0_newPlan_ = (self).AddToPlan(self.plan, f)
        (self).cabin = (self.cabin) | (_dafny.Set({f}))
        (self).plan = d_0_newPlan_

    def AddHallCall(self, f, d):
        d_0_newPlan_: _dafny.Seq
        d_0_newPlan_ = (self).AddToPlan(self.plan, f)
        if (d) == (HallDir_HallUp()):
            (self).hallUp = (self.hallUp) | (_dafny.Set({f}))
        elif True:
            (self).hallDown = (self.hallDown) | (_dafny.Set({f}))
        (self).plan = d_0_newPlan_

    def SetEmergency(self, on):
        if on:
            (self).mode = Mode_Emergency()
            (self).dir_ = Direction_Idle()
        elif True:
            (self).mode = Mode_Normal()

    def OpenDoor(self):
        (self).door = DoorState_Open()
        (self).doorTicks = (self).maxDoorTicks

    def CloseDoor(self):
        (self).door = DoorState_Closed()
        (self).doorTicks = 0

    def DoorTick(self):
        if (self.doorTicks) == (1):
            (self).door = DoorState_Closed()
            (self).doorTicks = 0
        elif True:
            (self).doorTicks = (self.doorTicks) - (1)

    def ServeHere(self):
        (self).cabin = (self.cabin) - (_dafny.Set({self.floor}))
        (self).hallUp = (self.hallUp) - (_dafny.Set({self.floor}))
        (self).hallDown = (self.hallDown) - (_dafny.Set({self.floor}))
        (self).plan = (self).RemoveFromPlan(self.plan, self.floor)

    def MoveOneUp(self):
        (self).dir_ = Direction_Up()
        (self).floor = (self.floor) + (1)
        (self).doorTicks = 0

    def MoveOneDown(self):
        (self).dir_ = Direction_Down()
        (self).floor = (self.floor) - (1)
        (self).doorTicks = 0

    def Stop(self):
        (self).dir_ = Direction_Idle()

    def DeterministicStep(self):
        if (self.mode) == (Mode_Emergency()):
            (self).Stop()
            return
        if (self.door) == (DoorState_Open()):
            (self).DoorTick()
            (self).dir_ = Direction_Idle()
            return
        if (self).RequestedHere():
            (self).dir_ = Direction_Idle()
            (self).OpenDoor()
            (self).ServeHere()
            return
        if not((self).HasRequests()):
            (self).Stop()
            return
        d_0_t_: int
        d_0_t_ = (self).NearestRequest()
        if (d_0_t_) > (self.floor):
            (self).MoveOneUp()
        elif (d_0_t_) < (self.floor):
            (self).MoveOneDown()
        elif True:
            (self).Stop()

    @property
    def minFloor(self):
        return self._minFloor
    @property
    def maxFloor(self):
        return self._maxFloor
    @property
    def maxDoorTicks(self):
        return self._maxDoorTicks
