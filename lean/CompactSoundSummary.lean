import Mathlib.Data.Set.Lattice

/-!
# Compact sound summary reuse

This file formalizes Propositions 1--5 in the compact proof note under
`../doc/main.tex`.

The development is domain-independent.  Concrete states are observed field by
field, which gives the paper's agreement relation and `ProjClose`.  The
analyzer, `relate`, and `filter` remain parameters.  Their paper properties are
explicit hypotheses of the corresponding theorems.
-/

namespace CompactSoundSummary

universe uField uValue uState uAbs

variable {Field : Type uField}
variable {Value : Type uValue}
variable {State : Type uState}
variable {Abs : Type uAbs}

/-! ## Concrete semantics and agreement closure -/

/-- Two states agree on `A` when every field in `A` has the same observation. -/
def Agree (observe : State → Field → Value) (A : Set Field)
    (i j : State) : Prop :=
  ∀ f, f ∈ A → observe i f = observe j f

/-- All states that agree on `A` with some state in `X`. -/
def projClose (observe : State → Field → Value) (A : Set Field)
    (X : Set State) : Set State :=
  {j | ∃ i ∈ X, Agree observe A i j}

/-- Collecting semantics induced by the concrete transition relation. -/
def collect (step : State → State → Prop) (X : Set State) : Set State :=
  {o | ∃ i ∈ X, step i o}

theorem mem_projClose_self (observe : State → Field → Value)
    {A : Set Field} {X : Set State} :
    X ⊆ projClose observe A X := by
  intro i hi
  exact ⟨i, hi, fun _ _ => rfl⟩

theorem projClose_mono (observe : State → Field → Value)
    {A : Set Field} {X Y : Set State} (hXY : X ⊆ Y) :
    projClose observe A X ⊆ projClose observe A Y := by
  intro j hj
  rcases hj with ⟨i, hi, hagree⟩
  exact ⟨i, hXY hi, hagree⟩

theorem collect_mono (step : State → State → Prop)
    {X Y : Set State} (hXY : X ⊆ Y) :
    collect step X ⊆ collect step Y := by
  intro o ho
  rcases ho with ⟨i, hi, hstep⟩
  exact ⟨i, hXY hi, hstep⟩

/-! ## Semantic specifications -/

/-- Paper definition (SE). -/
def SemanticExpand (step : State → State → Prop)
    (observe : State → Field → Value) (B : Set Field)
    (P : Set State) (A : Set Field) : Prop :=
  collect step (projClose observe A P) ⊆
    projClose observe B (collect step P)

def SoundFilter (observe : State → Field → Value)
    (gamma : Abs → Set State) (B : Set Field) (S T : Abs) : Prop :=
  projClose observe B (gamma S) ⊆ gamma T

def ExactFilter (observe : State → Field → Value)
    (gamma : Abs → Set State) (B : Set Field) (S T : Abs) : Prop :=
  gamma T = projClose observe B (gamma S)

/-- Paper definition (SR). -/
def SoundReuse (step : State → State → Prop) (gamma : Abs → Set State)
    (J result : Abs) : Prop :=
  collect step (gamma J) ⊆ gamma result

/-! ## Replay set construction -/

def ReplayClosure (relate : Set Field → Abs → Set Field)
    (R A : Set Field) (I : Abs) : Prop :=
  R ⊆ A ∧ relate A I ⊆ A

def ReadWriteExpansion (step : State → State → Prop)
    (observe : State → Field → Value) (R W : Set Field) : Prop :=
  ∀ A P, R ⊆ A → SemanticExpand step observe (A ∪ W) P A

/-- `A = Field` is always a (possibly coarse) solution of Replay Closure. -/
theorem replayClosure_univ (relate : Set Field → Abs → Set Field)
    (R : Set Field) (I : Abs) :
    ReplayClosure relate R Set.univ I := by
  constructor <;> intro f _ <;> trivial

/-- Proposition 1: Replay set correctness. -/
theorem replay_set_correctness
    (step : State → State → Prop) (observe : State → Field → Value)
    (gamma : Abs → Set State) (relate : Set Field → Abs → Set Field)
    (R W A : Set Field) (I : Abs)
    (hRW : ReadWriteExpansion step observe R W)
    (hClosure : ReplayClosure relate R A I) :
    SemanticExpand step observe (A ∪ W) (gamma I) A := by
  exact hRW A (gamma I) hClosure.1

/-! ## Filter construction -/

def FilterSound (observe : State → Field → Value)
    (gamma : Abs → Set State) (filter : Set Field → Abs → Abs) : Prop :=
  ∀ B S, SoundFilter observe gamma B S (filter B S)

def ClosedExact (observe : State → Field → Value)
    (gamma : Abs → Set State) (relate : Set Field → Abs → Set Field)
    (filter : Set Field → Abs → Abs) : Prop :=
  ∀ B S, relate B S ⊆ B → ExactFilter observe gamma B S (filter B S)

/-- Proposition 2: Exact filtering of the producer input. -/
theorem exact_filtering_of_producer_input
    (observe : State → Field → Value) (gamma : Abs → Set State)
    (relate : Set Field → Abs → Set Field)
    (filter : Set Field → Abs → Abs)
    (R A : Set Field) (I : Abs)
    (hClosure : ReplayClosure relate R A I)
    (hClosedExact : ClosedExact observe gamma relate filter) :
    ExactFilter observe gamma A I (filter A I) := by
  exact hClosedExact A I hClosure.2

/-! ## Summary production -/

def AnalyzeSound (step : State → State → Prop) (gamma : Abs → Set State)
    (analyze : Abs → Abs) : Prop :=
  ∀ S, collect step (gamma S) ⊆ gamma (analyze S)

/-- Proposition 3: Summary soundness.

Here `filter A I` is the stored input and
`filter (A ∪ W) (analyze I)` is the stored output.
-/
theorem summary_soundness
    (step : State → State → Prop) (observe : State → Field → Value)
    (gamma : Abs → Set State) (relate : Set Field → Abs → Set Field)
    (filter : Set Field → Abs → Abs) (analyze : Abs → Abs)
    (R W A : Set Field) (I : Abs)
    (hRW : ReadWriteExpansion step observe R W)
    (hClosure : ReplayClosure relate R A I)
    (hClosedExact : ClosedExact observe gamma relate filter)
    (hFilterSound : FilterSound observe gamma filter)
    (hAnalyzeSound : AnalyzeSound step gamma analyze) :
    collect step (gamma (filter A I)) ⊆
      gamma (filter (A ∪ W) (analyze I)) := by
  have hExact : gamma (filter A I) = projClose observe A (gamma I) :=
    exact_filtering_of_producer_input observe gamma relate filter R A I
      hClosure hClosedExact
  have hExpand :
      collect step (projClose observe A (gamma I)) ⊆
        projClose observe (A ∪ W) (collect step (gamma I)) :=
    replay_set_correctness step observe gamma relate R W A I hRW hClosure
  intro o ho
  rw [hExact] at ho
  have ho₁ : o ∈ projClose observe (A ∪ W) (collect step (gamma I)) :=
    hExpand ho
  have ho₂ : o ∈ projClose observe (A ∪ W) (gamma (analyze I)) :=
    projClose_mono observe (hAnalyzeSound I) ho₁
  exact hFilterSound (A ∪ W) (analyze I) ho₂

/-! ## Lookup and coarse reuse -/

def Lookup (filter : Set Field → Abs → Abs) (A : Set Field)
    (storedInput consumerInput : Abs) : Prop :=
  filter A consumerInput = storedInput

/-- The result returned on the accepted branch of coarse reuse. -/
def coarseReuse (storedOutput : Abs) : Abs :=
  storedOutput

theorem match_sound
    (observe : State → Field → Value) (gamma : Abs → Set State)
    (filter : Set Field → Abs → Abs) (A : Set Field)
    (storedInput consumerInput : Abs)
    (hFilterSound : FilterSound observe gamma filter)
    (hLookup : Lookup filter A storedInput consumerInput) :
    gamma consumerInput ⊆ gamma storedInput := by
  intro i hi
  have hiClose : i ∈ projClose observe A (gamma consumerInput) :=
    mem_projClose_self observe hi
  have hiFiltered : i ∈ gamma (filter A consumerInput) :=
    hFilterSound A consumerInput hiClose
  rw [hLookup] at hiFiltered
  exact hiFiltered

/-- Proposition 4: Sound summary reuse, given Summary Sound. -/
theorem sound_summary_reuse
    (step : State → State → Prop) (observe : State → Field → Value)
    (gamma : Abs → Set State) (filter : Set Field → Abs → Abs)
    (A : Set Field) (storedInput storedOutput consumerInput : Abs)
    (hFilterSound : FilterSound observe gamma filter)
    (hSummarySound : collect step (gamma storedInput) ⊆ gamma storedOutput)
    (hLookup : Lookup filter A storedInput consumerInput) :
    SoundReuse step gamma consumerInput
      (coarseReuse storedOutput) := by
  intro o ho
  apply hSummarySound
  apply collect_mono step
    (match_sound observe gamma filter A storedInput consumerInput
      hFilterSound hLookup)
  exact ho

/-! ## Frame-preserving reuse -/

/-- Successful execution preserves every field outside the write set. -/
def WriteFrame (step : State → State → Prop)
    (observe : State → Field → Value) (W : Set Field) : Prop :=
  ∀ i o, step i o → Agree observe (Set.univ \ W) i o

/-- The abstract combination contains the concrete intersection. -/
def MeetSound (gamma : Abs → Set State) (meet : Abs → Abs → Abs) : Prop :=
  ∀ S₁ S₂, gamma S₁ ∩ gamma S₂ ⊆ gamma (meet S₁ S₂)

/-- The abstract combination refines both operands. -/
def MeetReductive (gamma : Abs → Set State) (meet : Abs → Abs → Abs) : Prop :=
  ∀ S₁ S₂, gamma (meet S₁ S₂) ⊆ gamma S₁ ∩ gamma S₂

/-- The accepted branch combines the stored output with consumer information
on fields outside the write set. -/
def framePreservingReuse
    (meet : Abs → Abs → Abs) (filter : Set Field → Abs → Abs)
    (W : Set Field) (storedOutput consumerInput : Abs) : Abs :=
  meet storedOutput (filter (Set.univ \ W) consumerInput)

/-- Proposition 5: accepted frame-preserving reuse is sound and is at least as
precise as accepted coarse reuse. -/
theorem sound_and_precise_frame_preserving_reuse
    (step : State → State → Prop) (observe : State → Field → Value)
    (gamma : Abs → Set State) (filter : Set Field → Abs → Abs)
    (meet : Abs → Abs → Abs) (W : Set Field)
    (storedOutput consumerInput : Abs)
    (hFilterSound : FilterSound observe gamma filter)
    (hCoarseSound : SoundReuse step gamma consumerInput storedOutput)
    (hWriteFrame : WriteFrame step observe W)
    (hMeetSound : MeetSound gamma meet)
    (hMeetReductive : MeetReductive gamma meet) :
    SoundReuse step gamma consumerInput
        (framePreservingReuse meet filter W storedOutput consumerInput) ∧
      gamma (framePreservingReuse meet filter W storedOutput consumerInput) ⊆
        gamma (coarseReuse storedOutput) := by
  constructor
  · intro o ho
    have hoStored : o ∈ gamma storedOutput := hCoarseSound ho
    rcases ho with ⟨i, hi, hstep⟩
    have hoFrame :
        o ∈ gamma (filter (Set.univ \ W) consumerInput) :=
      hFilterSound (Set.univ \ W) consumerInput
        ⟨i, hi, hWriteFrame i o hstep⟩
    exact hMeetSound storedOutput
      (filter (Set.univ \ W) consumerInput) ⟨hoStored, hoFrame⟩
  · intro x hx
    exact (hMeetReductive storedOutput
      (filter (Set.univ \ W) consumerInput) hx).1

/-- End-to-end form of the final theorem.  It discharges Summary Sound with
Propositions 1--3 and then applies Proposition 4. -/
theorem end_to_end_sound_summary_reuse
    (step : State → State → Prop) (observe : State → Field → Value)
    (gamma : Abs → Set State) (relate : Set Field → Abs → Set Field)
    (filter : Set Field → Abs → Abs) (analyze : Abs → Abs)
    (R W A : Set Field) (producerInput consumerInput : Abs)
    (hRW : ReadWriteExpansion step observe R W)
    (hClosure : ReplayClosure relate R A producerInput)
    (hClosedExact : ClosedExact observe gamma relate filter)
    (hFilterSound : FilterSound observe gamma filter)
    (hAnalyzeSound : AnalyzeSound step gamma analyze)
    (hLookup : Lookup filter A (filter A producerInput) consumerInput) :
    SoundReuse step gamma consumerInput
      (coarseReuse (filter (A ∪ W) (analyze producerInput))) := by
  apply sound_summary_reuse step observe gamma filter A
    (filter A producerInput) (filter (A ∪ W) (analyze producerInput))
    consumerInput hFilterSound
  · exact summary_soundness step observe gamma relate filter analyze
      R W A producerInput hRW hClosure hClosedExact hFilterSound hAnalyzeSound
  · exact hLookup

/-- End-to-end P5, with P4 discharged by the preceding theorem. -/
theorem end_to_end_sound_frame_preserving_reuse
    (step : State → State → Prop) (observe : State → Field → Value)
    (gamma : Abs → Set State) (relate : Set Field → Abs → Set Field)
    (filter : Set Field → Abs → Abs) (analyze : Abs → Abs)
    (meet : Abs → Abs → Abs) (R W A : Set Field)
    (producerInput consumerInput : Abs)
    (hRW : ReadWriteExpansion step observe R W)
    (hClosure : ReplayClosure relate R A producerInput)
    (hClosedExact : ClosedExact observe gamma relate filter)
    (hFilterSound : FilterSound observe gamma filter)
    (hAnalyzeSound : AnalyzeSound step gamma analyze)
    (hWriteFrame : WriteFrame step observe W)
    (hMeetSound : MeetSound gamma meet)
    (hMeetReductive : MeetReductive gamma meet)
    (hLookup : Lookup filter A (filter A producerInput) consumerInput) :
    SoundReuse step gamma consumerInput
        (framePreservingReuse meet filter W
          (filter (A ∪ W) (analyze producerInput)) consumerInput) ∧
      gamma (framePreservingReuse meet filter W
          (filter (A ∪ W) (analyze producerInput)) consumerInput) ⊆
        gamma (coarseReuse (filter (A ∪ W) (analyze producerInput))) := by
  apply sound_and_precise_frame_preserving_reuse step observe gamma filter meet
    W (filter (A ∪ W) (analyze producerInput)) consumerInput
    hFilterSound
  · exact end_to_end_sound_summary_reuse step observe gamma relate filter analyze
      R W A producerInput consumerInput hRW hClosure hClosedExact
      hFilterSound hAnalyzeSound hLookup
  · exact hWriteFrame
  · exact hMeetSound
  · exact hMeetReductive

end CompactSoundSummary
