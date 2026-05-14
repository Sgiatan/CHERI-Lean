-- This module serves as the root of the `Formalisation` library.
-- Import modules here that should be built as part of the library.
import Mathlib

abbrev Address := Nat
abbrev ObjectType := Nat

-- Object types are 18-bit in CHERI-MIPS (need to truncate full addresses)
def cursorToObjectType (n : Address) : ObjectType :=
    n % (2^18)

structure CapBounds where
    Base : Address
    Length : Nat
deriving Repr, BEq

inductive PermBit where
    | PermitLoad
    | PermitStore
    | PermitLoadCapability
    | PermitStoreCapability
    | PermitExecute
    | PermitSeal
    | PermitUnseal
    | PermitAccessSystemRegisters
    | PermitCCall
deriving Repr, BEq, DecidableEq

structure Capability where
    Tag : Bool
    IsSealed : Bool
    CapBounds : CapBounds
    Offset : Nat
    Perms : Finset PermBit
    UPerms : Finset PermBit
    ObjectType : ObjectType
    Reserved : Nat
deriving BEq

def getCursor (c : Capability) : Address :=
    c.CapBounds.Base + c.Offset

abbrev RegIndex := Nat

inductive AbstractAction where
    | LoadDataAction (auth : RegIndex) (a : Address) (l : Nat)
    | StoreDataAction (auth : RegIndex) (a : Address) (l : Nat)
    | LoadCapAction (auth : RegIndex) (a : Address) (r : RegIndex)
    | StoreCapAction (auth : RegIndex) (r : RegIndex) (a : Address)
    | RestrictCapAction (r r' : RegIndex)
    | SealCapAction (auth : RegIndex) (r r' : RegIndex)
    | UnsealCapAction (auth : RegIndex) (r r' : RegIndex)
    | RaiseException
    | InvokeCapability (r r' : RegIndex)
deriving Repr

inductive InstructionIntention where
    | SwitchDomain (a : AbstractAction)
    | KeepDomain (actions : List AbstractAction)
deriving Repr

-- b ⊆ b'
def boundInside (b b' : CapBounds) : Prop :=
    b'.Base ≤ b.Base ∧ (b.Base + b.Length) ≤ (b'.Base + b'.Length)

-- c ≤ c'
def capLE (c c' : Capability) : Prop :=
    ¬ c.Tag
    ∨ c = c'
    ∨ ( c.Tag ∧ c'.Tag
      ∧ ¬ c.IsSealed ∧ ¬ c'.IsSealed
      ∧ boundInside c.CapBounds c'.CapBounds
      ∧ c.Perms ⊆ c'.Perms
      ∧ c.UPerms ⊆ c'.UPerms
      ∧ c.ObjectType == c'.ObjectType
      ∧ c.Reserved == c'.Reserved
      )

theorem boundInside_transitive (b b' b'' : CapBounds) : boundInside b b' → boundInside b' b'' → boundInside b b'' :=
    by
        intro h1 h2
        unfold boundInside at h1 h2 ⊢
        obtain ⟨ start1, end1 ⟩ := h1
        obtain ⟨ start2, end2 ⟩ := h2
        have start := Nat.le_trans start2 start1
        have ends := Nat.le_trans end1 end2
        constructor
        · exact start
        · exact ends



theorem capLE_reflexivity (c : Capability) : capLE c c :=
    by
        unfold capLE
        apply Or.inr
        apply Or.inl
        rfl

theorem capLE_transitivity (c c' c'' : Capability) : capLE c c' ∧ capLE c' c'' → capLE c c'' :=
    by
        apply And.elim
        intro h1 h2
        unfold capLE at h1 h2 ⊢
        cases h1

        -- c has no tag, so c ≤ c'' regardless of c''
        case inl h1_invalid =>
            apply Or.inl
            exact h1_invalid

        -- c has a tag, so we need to consider the cases for c'
        case inr h1_valid =>
            cases h1_valid

            -- c' = c, so trivially c ≤ c''
            case inl h1_eq =>
                rw [Eq.comm] at h1_eq
                rw [h1_eq] at h2
                exact h2

            case inr h1_le =>
                cases h2
                -- c' cannot be invalid if c is valid, so this case is a contradiction
                case inl h2_invalid =>
                    simp_all
                case inr h2_valid =>
                    cases h2_valid
                    case inl h2_eq =>
                        simp_all
                    case inr h2_le =>
                        obtain ⟨ cvalid,
                                 c'valid,
                                 cunsealed,
                                 c'unsealed,
                                 boundsInside1,
                                 permsLE1,
                                 upermsLE1,
                                 objectsMatch1,
                                 reservedMatch1 ⟩ := h1_le
                        obtain ⟨ c'valid,
                                 c''valid,
                                 c'unsealed,
                                 c''unsealed,
                                 boundsInside2,
                                 permsLE2,
                                 upermsLE2,
                                 objectsMatch2,
                                 reservedMatch2 ⟩ := h2_le
                        apply Or.inr
                        apply Or.inr
                        refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
                        · exact cvalid
                        · exact c''valid
                        · exact cunsealed
                        · exact c''unsealed
                        · exact boundInside_transitive c.CapBounds c'.CapBounds c''.CapBounds boundsInside1 boundsInside2
                        · exact Finset.Subset.trans permsLE1 permsLE2
                        · exact Finset.Subset.trans upermsLE1 upermsLE2
                        · rw [beq_iff_eq] at objectsMatch1 objectsMatch2 ⊢
                          rw [objectsMatch2] at objectsMatch1
                          exact objectsMatch1
                        · rw [beq_iff_eq] at reservedMatch1 reservedMatch2 ⊢
                          rw [reservedMatch2] at reservedMatch1
                          exact reservedMatch1


structure Memory where
    MemData : Address → Nat
    MemCap  : Address → Capability
    MemTag  : Address → Bool

structure MachineState where
    -- General purpose registers
    NormalCapReg  : RegIndex → Capability
    DataReg       : RegIndex → Nat

    -- Special capability registers
    PCC           : Capability   -- program counter capability
    DDC           : Capability   -- default data capability (special reg 0)
    TLSC          : Capability   -- special reg 1
    EPCC          : Capability   -- exception PC capability (special reg 31)
    KCC           : Capability   -- kernel code capability

    -- Control state
    PC            : Nat
    KernelMode    : Bool
    AccessToCU0   : Bool         -- CP0 access flag
    EXL           : Bool         -- exception level flag
    -- Memory
    Mem           : Memory


opaque StateIsValid (s : MachineState) : Prop

-- gets addresses in segment starting at a, of length ln
opaque MemSegment (a : Address) (ln : Nat) : Finset Address

def addrIn (a : Address) (b : CapBounds) : Prop :=
    a ∈ MemSegment b.Base b.Length

-- maps virtual addresses within cap bounds to physical addresses
opaque TranslateAddresses : CapBounds → MachineState → Finset Address

-- rounds down to nearest capability-aligned address
opaque GetCapAddress : Address → Address

opaque ExtendCapAddress : Address → Address

opaque UCast : ObjectType → Address

def unsealCap (c : Capability) : Capability :=
    { c with IsSealed := false, ObjectType := 0 }

def sealCap (c : Capability) (t : Address) : Capability :=
    { c with IsSealed := true, ObjectType := t }

section properties
                -- Initial state       Actions            Result state
    variable (sem : MachineState → InstructionIntention → MachineState → Prop)

    axiom RestrictCapProp :
        ∀ (s s' : MachineState) (actions : List AbstractAction) (r r' : RegIndex),
        StateIsValid s
            → sem s (InstructionIntention.KeepDomain actions) s'
            → AbstractAction.RestrictCapAction r r' ∈ actions
        → capLE (s'.NormalCapReg r') (s.NormalCapReg r)

    axiom StoreDataProp :
        ∀ (s s' : MachineState) (actions : List AbstractAction) (auth : RegIndex) (a : Address) (ln : Nat),
        StateIsValid s
            → sem s (InstructionIntention.KeepDomain actions) s'
            → AbstractAction.StoreDataAction auth a ln ∈ actions
        → (s.NormalCapReg auth).Tag
            ∧ ¬(s.NormalCapReg auth).IsSealed
            ∧ PermBit.PermitStore ∈ (s.NormalCapReg auth).Perms
            ∧ ln ≠ 0
            ∧ MemSegment a ln ⊆ TranslateAddresses (s.NormalCapReg auth).CapBounds s
            ∧ ¬ (s'.Mem.MemCap (GetCapAddress a)).Tag
            ∨ (s'.Mem.MemCap (GetCapAddress a)) = (s.Mem.MemCap (GetCapAddress a))

    axiom StoreCapProp :
        ∀ (s s' : MachineState) (actions : List AbstractAction) (auth : RegIndex) (r : RegIndex) (a : Address),
        StateIsValid s
            → sem s (InstructionIntention.KeepDomain actions) s'
            → AbstractAction.StoreCapAction auth r a ∈ actions
        → (s.NormalCapReg auth).Tag
            ∧ ¬(s.NormalCapReg auth).IsSealed
            ∧ PermBit.PermitStore ∈ (s.NormalCapReg auth).Perms
            ∧ PermBit.PermitStoreCapability ∈ (s.NormalCapReg auth).Perms
            ∧ MemSegment (ExtendCapAddress a) 32 ⊆ TranslateAddresses (s.NormalCapReg auth).CapBounds s
            ∧ s'.Mem.MemCap a = s.NormalCapReg r

    axiom LoadDataProp :
        ∀ (s s' : MachineState) (actions : List AbstractAction) (auth : RegIndex) (a : Address) (ln : Nat),
        StateIsValid s
            → sem s (InstructionIntention.KeepDomain actions) s'
            → AbstractAction.LoadDataAction auth a ln ∈ actions
        → (s.NormalCapReg auth).Tag
            ∧ ¬(s.NormalCapReg auth).IsSealed
            ∧ PermBit.PermitLoad ∈ (s.NormalCapReg auth).Perms
            ∧ ln ≠ 0
            ∧ MemSegment a ln ⊆ TranslateAddresses (s.NormalCapReg auth).CapBounds s
            ∧ ¬ (s'.Mem.MemCap (GetCapAddress a)).Tag
            ∨ (s'.Mem.MemCap (GetCapAddress a)) = (s.Mem.MemCap (GetCapAddress a))

    axiom LoadCapProp :
        ∀ (s s' : MachineState) (actions : List AbstractAction) (auth : RegIndex) (r : RegIndex) (a : Address),
        StateIsValid s
            → sem s (InstructionIntention.KeepDomain actions) s'
            → AbstractAction.LoadCapAction auth a r ∈ actions
        → (s.NormalCapReg auth).Tag
            ∧ ¬(s.NormalCapReg auth).IsSealed
            ∧ PermBit.PermitLoad ∈ (s.NormalCapReg auth).Perms
            ∧ PermBit.PermitLoadCapability ∈ (s.NormalCapReg auth).Perms
            ∧ MemSegment (ExtendCapAddress a) 32 ⊆ TranslateAddresses (s.NormalCapReg auth).CapBounds s
            ∧ s'.Mem.MemCap a = s.NormalCapReg r

    axiom UnsealCapProp :
        ∀ (s s' : MachineState) (actions : List AbstractAction) (auth : RegIndex) (r r' : RegIndex),
        StateIsValid s
            → sem s (InstructionIntention.KeepDomain actions) s'
            → AbstractAction.UnsealCapAction auth r r' ∈ actions
        → (s.NormalCapReg auth).Tag
            ∧ ¬(s.NormalCapReg auth).IsSealed
            ∧ PermBit.PermitUnseal ∈ (s.NormalCapReg auth).Perms
            ∧ addrIn (UCast ((s.NormalCapReg r).ObjectType)) (s.NormalCapReg auth).CapBounds
            ∧ (s.NormalCapReg r).IsSealed
            ∧ capLE (s'.NormalCapReg r') (unsealCap (s.NormalCapReg r))

    axiom SealCapProp :
        ∀ (s s' : MachineState) (actions : List AbstractAction) (auth : RegIndex) (r r' : RegIndex),
        StateIsValid s
            → sem s (InstructionIntention.KeepDomain actions) s'
            → AbstractAction.SealCapAction auth r r' ∈ actions
        →
            (s.NormalCapReg auth).Tag
            ∧ ¬(s.NormalCapReg auth).IsSealed
            ∧ PermBit.PermitSeal ∈ (s.NormalCapReg auth).Perms
            ∧ addrIn (UCast (getCursor (s.NormalCapReg auth))) (s.NormalCapReg auth).CapBounds
            ∧ ¬(s.NormalCapReg r).IsSealed
            ∧ s'.NormalCapReg r' = sealCap (s.NormalCapReg r) (cursorToObjectType (getCursor (s.NormalCapReg auth)))

end properties
