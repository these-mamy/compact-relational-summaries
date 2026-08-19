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

/-- The displayed Separation diagnostic.  It is independent of P1--P5. -/
def Separation (observe : State → Field → Value)
    (gamma : Abs → Set State) (A : Set Field) (S : Abs) : Prop :=
  gamma S =
    projClose observe A (gamma S) ∩
      projClose observe (Set.univ \ A) (gamma S)

/-- Weak producer-side upper bound used by Summary Sound. -/
def ProductionInput (observe : State → Field → Value)
    (gamma : Abs → Set State) (A : Set Field)
    (producerInput storedInput : Abs) : Prop :=
  gamma storedInput ⊆ projClose observe A (gamma producerInput)

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

/-- Summary Sound from the weakest producer-input bound used by the proof. -/
theorem summary_soundness_from_production_input
    (step : State → State → Prop) (observe : State → Field → Value)
    (gamma : Abs → Set State) (filter : Set Field → Abs → Abs)
    (analyze : Abs → Abs) (A W : Set Field)
    (producerInput storedInput : Abs)
    (hProductionInput :
      ProductionInput observe gamma A producerInput storedInput)
    (hExpand : SemanticExpand step observe (A ∪ W)
      (gamma producerInput) A)
    (hFilterSound : FilterSound observe gamma filter)
    (hAnalyzeSound : AnalyzeSound step gamma analyze) :
    collect step (gamma storedInput) ⊆
      gamma (filter (A ∪ W) (analyze producerInput)) := by
  intro o ho
  have ho₀ : o ∈ collect step (projClose observe A (gamma producerInput)) :=
    collect_mono step hProductionInput ho
  have ho₁ : o ∈ projClose observe (A ∪ W)
      (collect step (gamma producerInput)) :=
    hExpand ho₀
  have ho₂ : o ∈ projClose observe (A ∪ W)
      (gamma (analyze producerInput)) :=
    projClose_mono observe (hAnalyzeSound producerInput) ho₁
  exact hFilterSound (A ∪ W) (analyze producerInput) ho₂

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
  have hProductionInput : ProductionInput observe gamma A I (filter A I) := by
    intro x hx
    rw [hExact] at hx
    exact hx
  have hExpand :
      collect step (projClose observe A (gamma I)) ⊆
        projClose observe (A ∪ W) (collect step (gamma I)) :=
    replay_set_correctness step observe gamma relate R W A I hRW hClosure
  exact summary_soundness_from_production_input step observe gamma filter
    analyze A W I (filter A I) hProductionInput hExpand hFilterSound
    hAnalyzeSound

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

/-- Coarse reuse needs only the semantic Match Sound inclusion. -/
theorem sound_summary_reuse_from_match
    (step : State → State → Prop) (gamma : Abs → Set State)
    (storedInput storedOutput consumerInput : Abs)
    (hMatch : gamma consumerInput ⊆ gamma storedInput)
    (hSummarySound : collect step (gamma storedInput) ⊆ gamma storedOutput) :
    SoundReuse step gamma consumerInput (coarseReuse storedOutput) := by
  intro o ho
  exact hSummarySound (collect_mono step hMatch ho)

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
  exact sound_summary_reuse_from_match step gamma storedInput storedOutput
    consumerInput
    (match_sound observe gamma filter A storedInput consumerInput
      hFilterSound hLookup)
    hSummarySound

/-! ## Frame-preserving reuse -/

/-- Successful execution preserves every field outside the write set. -/
def WriteFrame (step : State → State → Prop)
    (observe : State → Field → Value) (W : Set Field) : Prop :=
  ∀ i o, step i o → Agree observe (Set.univ \ W) i o

/-- The selected consumer-frame filter admits no state beyond its closure. -/
def FrameFilterReductive (observe : State → Field → Value)
    (gamma : Abs → Set State) (filter : Set Field → Abs → Abs)
    (W : Set Field) (consumerInput : Abs) : Prop :=
  gamma (filter (Set.univ \ W) consumerInput) ⊆
    projClose observe (Set.univ \ W) (gamma consumerInput)

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

/-- Proposition 5: accepted frame-preserving reuse is sound, refines coarse
reuse, and satisfies the concrete consumer-frame constraint. -/
theorem sound_and_precise_frame_preserving_reuse
    (step : State → State → Prop) (observe : State → Field → Value)
    (gamma : Abs → Set State) (filter : Set Field → Abs → Abs)
    (meet : Abs → Abs → Abs) (W : Set Field)
    (storedOutput consumerInput : Abs)
    (hFilterSound : FilterSound observe gamma filter)
    (hCoarseSound : SoundReuse step gamma consumerInput storedOutput)
    (hWriteFrame : WriteFrame step observe W)
    (hFrameFilterReductive :
      FrameFilterReductive observe gamma filter W consumerInput)
    (hMeetSound : MeetSound gamma meet)
    (hMeetReductive : MeetReductive gamma meet) :
    SoundReuse step gamma consumerInput
        (framePreservingReuse meet filter W storedOutput consumerInput) ∧
      gamma (framePreservingReuse meet filter W storedOutput consumerInput) ⊆
        gamma (coarseReuse storedOutput) ∧
      gamma (framePreservingReuse meet filter W storedOutput consumerInput) ⊆
        projClose observe (Set.univ \ W) (gamma consumerInput) := by
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
  · constructor
    · intro x hx
      exact (hMeetReductive storedOutput
        (filter (Set.univ \ W) consumerInput) hx).1
    · intro x hx
      exact hFrameFilterReductive
        (hMeetReductive storedOutput
          (filter (Set.univ \ W) consumerInput) hx).2

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
    (hFrameFilterReductive :
      FrameFilterReductive observe gamma filter W consumerInput)
    (hMeetSound : MeetSound gamma meet)
    (hMeetReductive : MeetReductive gamma meet)
    (hLookup : Lookup filter A (filter A producerInput) consumerInput) :
    SoundReuse step gamma consumerInput
        (framePreservingReuse meet filter W
          (filter (A ∪ W) (analyze producerInput)) consumerInput) ∧
      gamma (framePreservingReuse meet filter W
          (filter (A ∪ W) (analyze producerInput)) consumerInput) ⊆
        gamma (coarseReuse (filter (A ∪ W) (analyze producerInput))) ∧
      gamma (framePreservingReuse meet filter W
          (filter (A ∪ W) (analyze producerInput)) consumerInput) ⊆
        projClose observe (Set.univ \ W) (gamma consumerInput) := by
  apply sound_and_precise_frame_preserving_reuse step observe gamma filter meet
    W (filter (A ∪ W) (analyze producerInput)) consumerInput
    hFilterSound
  · exact end_to_end_sound_summary_reuse step observe gamma relate filter analyze
      R W A producerInput consumerInput hRW hClosure hClosedExact
      hFilterSound hAnalyzeSound hLookup
  · exact hWriteFrame
  · exact hFrameFilterReductive
  · exact hMeetSound
  · exact hMeetReductive

end CompactSoundSummary
