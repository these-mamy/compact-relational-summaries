prelude

/-!
This is the kernel-checkable, dependency-free version of the compact summary
reuse proof.  It starts with `prelude`, defines only the powerset operations
that the proof needs, and uses proof terms rather than imported tactics.
-/

namespace CompactSoundSummaryCore

universe uField uValue uState uAbs

abbrev PSet (α : Type u) : Type u := α → Prop

inductive Truth : Prop where
  | intro : Truth

inductive Conj (left right : Prop) : Prop where
  | intro : left → right → Conj left right

inductive Disj (left right : Prop) : Prop where
  | left : left → Disj left right
  | right : right → Disj left right

inductive Ex {α : Type u} (property : α → Prop) : Prop where
  | intro (witness : α) : property witness → Ex property

inductive Equal {α : Type u} (left : α) : α → Prop where
  | refl : Equal left left

inductive Falsity : Prop

def Conj.first {left right : Prop} (proof : Conj left right) : left :=
  Conj.rec (fun hleft _ => hleft) proof

def Conj.second {left right : Prop} (proof : Conj left right) : right :=
  Conj.rec (fun _ hright => hright) proof

def Ex.eliminate {α : Type u} {property : α → Prop} {result : Prop}
    (proof : Ex property) (next : ∀ witness, property witness → result) : result :=
  Ex.rec next proof

def Equal.substitute {α : Type u} {left right : α}
    (proof : Equal left right) (property : α → Prop)
    (atLeft : property left) : property right :=
  Equal.rec atLeft proof

abbrev subset {α : Type u} (X Y : PSet α) : Prop :=
  ∀ x, X x → Y x

def univ {α : Type u} : PSet α :=
  fun _ => Truth

def union {α : Type u} (X Y : PSet α) : PSet α :=
  fun x => Disj (X x) (Y x)

def inter {α : Type u} (X Y : PSet α) : PSet α :=
  fun x => Conj (X x) (Y x)

def outside {α : Type u} (W : PSet α) : PSet α :=
  fun f => W f → Falsity

variable {Field : Type uField}
variable {Value : Type uValue}
variable {State : Type uState}
variable {Abs : Type uAbs}

def Agree (observe : State → Field → Value) (A : PSet Field)
    (i j : State) : Prop :=
  ∀ f, A f → Equal (observe i f) (observe j f)

def projClose (observe : State → Field → Value) (A : PSet Field)
    (X : PSet State) : PSet State :=
  fun j => Ex (fun i => Conj (X i) (Agree observe A i j))

def collect (step : State → State → Prop) (X : PSet State) : PSet State :=
  fun o => Ex (fun i => Conj (X i) (step i o))

theorem mem_projClose_self (observe : State → Field → Value)
    {A : PSet Field} {X : PSet State} :
    subset X (projClose observe A X) :=
  fun i hi => Ex.intro i (Conj.intro hi (fun _ _ => Equal.refl))

theorem projClose_mono (observe : State → Field → Value)
    {A : PSet Field} {X Y : PSet State} (hXY : subset X Y) :
    subset (projClose observe A X) (projClose observe A Y) :=
  fun _ hj => Ex.eliminate hj (fun i hboth =>
    Ex.intro i (Conj.intro (hXY i (Conj.first hboth)) (Conj.second hboth)))

theorem collect_mono (step : State → State → Prop)
    {X Y : PSet State} (hXY : subset X Y) :
    subset (collect step X) (collect step Y) :=
  fun _ ho => Ex.eliminate ho (fun i hboth =>
    Ex.intro i (Conj.intro (hXY i (Conj.first hboth)) (Conj.second hboth)))

abbrev SemanticExpand (step : State → State → Prop)
    (observe : State → Field → Value) (B : PSet Field)
    (P : PSet State) (A : PSet Field) : Prop :=
  subset (collect step (projClose observe A P))
    (projClose observe B (collect step P))

abbrev SoundFilter (observe : State → Field → Value)
    (gamma : Abs → PSet State) (B : PSet Field) (S T : Abs) : Prop :=
  subset (projClose observe B (gamma S)) (gamma T)

abbrev ExactFilter (observe : State → Field → Value)
    (gamma : Abs → PSet State) (B : PSet Field) (S T : Abs) : Prop :=
  Equal (gamma T) (projClose observe B (gamma S))

/-- The displayed Separation diagnostic.  It is independent of P1--P5. -/
abbrev Separation (observe : State → Field → Value)
    (gamma : Abs → PSet State) (A : PSet Field) (S : Abs) : Prop :=
  Equal (gamma S)
    (inter (projClose observe A (gamma S))
      (projClose observe (outside A) (gamma S)))

/-- Weak producer-side upper bound used by Summary Sound. -/
abbrev ProductionInput (observe : State → Field → Value)
    (gamma : Abs → PSet State) (A : PSet Field)
    (producerInput storedInput : Abs) : Prop :=
  subset (gamma storedInput) (projClose observe A (gamma producerInput))

abbrev SoundReuse (step : State → State → Prop) (gamma : Abs → PSet State)
    (J result : Abs) : Prop :=
  subset (collect step (gamma J)) (gamma result)

def ReplayClosure (relate : PSet Field → Abs → PSet Field)
    (R A : PSet Field) (I : Abs) : Prop :=
  Conj (subset R A) (subset (relate A I) A)

abbrev ReadWriteExpansion (step : State → State → Prop)
    (observe : State → Field → Value) (R W : PSet Field) : Prop :=
  ∀ A P, subset R A →
    SemanticExpand step observe (union A W) P A

theorem replayClosure_univ (relate : PSet Field → Abs → PSet Field)
    (R : PSet Field) (I : Abs) :
    ReplayClosure relate R univ I :=
  Conj.intro (fun _ _ => Truth.intro) (fun _ _ => Truth.intro)

/-- Proposition 1. -/
theorem replay_set_correctness
    (step : State → State → Prop) (observe : State → Field → Value)
    (gamma : Abs → PSet State) (relate : PSet Field → Abs → PSet Field)
    (R W A : PSet Field) (I : Abs)
    (hRW : ReadWriteExpansion step observe R W)
    (hClosure : ReplayClosure relate R A I) :
    SemanticExpand step observe (union A W) (gamma I) A :=
  hRW A (gamma I) (Conj.first hClosure)

abbrev FilterSound (observe : State → Field → Value)
    (gamma : Abs → PSet State) (filter : PSet Field → Abs → Abs) : Prop :=
  ∀ B S, SoundFilter observe gamma B S (filter B S)

abbrev ClosedExact (observe : State → Field → Value)
    (gamma : Abs → PSet State)
    (relate : PSet Field → Abs → PSet Field)
    (filter : PSet Field → Abs → Abs) : Prop :=
  ∀ B S, subset (relate B S) B →
    ExactFilter observe gamma B S (filter B S)

/-- Proposition 2. -/
theorem exact_filtering_of_producer_input
    (observe : State → Field → Value) (gamma : Abs → PSet State)
    (relate : PSet Field → Abs → PSet Field)
    (filter : PSet Field → Abs → Abs)
    (R A : PSet Field) (I : Abs)
    (hClosure : ReplayClosure relate R A I)
    (hClosedExact : ClosedExact observe gamma relate filter) :
    ExactFilter observe gamma A I (filter A I) :=
  hClosedExact A I (Conj.second hClosure)

abbrev AnalyzeSound (step : State → State → Prop) (gamma : Abs → PSet State)
    (analyze : Abs → Abs) : Prop :=
  ∀ S, subset (collect step (gamma S)) (gamma (analyze S))

/-- Summary Sound from the weakest producer-input bound used by the proof. -/
theorem summary_soundness_from_production_input
    (step : State → State → Prop) (observe : State → Field → Value)
    (gamma : Abs → PSet State) (filter : PSet Field → Abs → Abs)
    (analyze : Abs → Abs) (A W : PSet Field)
    (producerInput storedInput : Abs)
    (hProductionInput : ProductionInput observe gamma A producerInput storedInput)
    (hExpand : SemanticExpand step observe (union A W)
      (gamma producerInput) A)
    (hFilterSound : FilterSound observe gamma filter)
    (hAnalyzeSound : AnalyzeSound step gamma analyze) :
    subset (collect step (gamma storedInput))
      (gamma (filter (union A W) (analyze producerInput))) :=
  fun o ho =>
    have ho0 : collect step (projClose observe A (gamma producerInput)) o :=
      collect_mono step hProductionInput o ho
    have ho1 : projClose observe (union A W)
        (collect step (gamma producerInput)) o :=
      hExpand o ho0
    have ho2 : projClose observe (union A W)
        (gamma (analyze producerInput)) o :=
      projClose_mono observe (hAnalyzeSound producerInput) o ho1
    hFilterSound (union A W) (analyze producerInput) o ho2

/-- Proposition 3. -/
theorem summary_soundness
    (step : State → State → Prop) (observe : State → Field → Value)
    (gamma : Abs → PSet State) (relate : PSet Field → Abs → PSet Field)
    (filter : PSet Field → Abs → Abs) (analyze : Abs → Abs)
    (R W A : PSet Field) (I : Abs)
    (hRW : ReadWriteExpansion step observe R W)
    (hClosure : ReplayClosure relate R A I)
    (hClosedExact : ClosedExact observe gamma relate filter)
    (hFilterSound : FilterSound observe gamma filter)
    (hAnalyzeSound : AnalyzeSound step gamma analyze) :
    subset (collect step (gamma (filter A I)))
      (gamma (filter (union A W) (analyze I))) :=
  have hExact : Equal (gamma (filter A I)) (projClose observe A (gamma I)) :=
    exact_filtering_of_producer_input observe gamma relate filter R A I
      hClosure hClosedExact
  have hProductionInput : ProductionInput observe gamma A I (filter A I) :=
    fun x hx => Equal.substitute hExact (fun inputs => inputs x) hx
  have hExpand :=
    replay_set_correctness step observe gamma relate R W A I hRW hClosure
  summary_soundness_from_production_input step observe gamma filter analyze A W
    I (filter A I) hProductionInput hExpand hFilterSound hAnalyzeSound

def Lookup (filter : PSet Field → Abs → Abs) (A : PSet Field)
    (storedInput consumerInput : Abs) : Prop :=
  Equal (filter A consumerInput) storedInput

theorem match_sound
    (observe : State → Field → Value) (gamma : Abs → PSet State)
    (filter : PSet Field → Abs → Abs) (A : PSet Field)
    (storedInput consumerInput : Abs)
    (hFilterSound : FilterSound observe gamma filter)
    (hLookup : Lookup filter A storedInput consumerInput) :
    subset (gamma consumerInput) (gamma storedInput) :=
  fun i hi =>
    have hiClose : projClose observe A (gamma consumerInput) i :=
      mem_projClose_self observe i hi
    have hiFiltered : gamma (filter A consumerInput) i :=
      hFilterSound A consumerInput i hiClose
    Equal.substitute hLookup (fun input => gamma input i) hiFiltered

/-- Coarse reuse needs only the semantic Match Sound inclusion. -/
theorem sound_summary_reuse_from_match
    (step : State → State → Prop) (gamma : Abs → PSet State)
    (storedInput storedOutput consumerInput : Abs)
    (hMatch : subset (gamma consumerInput) (gamma storedInput))
    (hSummarySound : subset (collect step (gamma storedInput))
      (gamma storedOutput)) :
    SoundReuse step gamma consumerInput storedOutput :=
  fun o ho => hSummarySound o (collect_mono step hMatch o ho)

/-- Proposition 4. -/
theorem sound_summary_reuse
    (step : State → State → Prop) (observe : State → Field → Value)
    (gamma : Abs → PSet State) (filter : PSet Field → Abs → Abs)
    (A : PSet Field) (storedInput storedOutput consumerInput : Abs)
    (hFilterSound : FilterSound observe gamma filter)
    (hSummarySound : subset (collect step (gamma storedInput))
      (gamma storedOutput))
    (hLookup : Lookup filter A storedInput consumerInput) :
    SoundReuse step gamma consumerInput storedOutput :=
  sound_summary_reuse_from_match step gamma storedInput storedOutput
    consumerInput
    (match_sound observe gamma filter A storedInput consumerInput
      hFilterSound hLookup)
    hSummarySound

abbrev WriteFrame (step : State → State → Prop)
    (observe : State → Field → Value) (W : PSet Field) : Prop :=
  ∀ i o, step i o → Agree observe (outside W) i o

/-- The selected consumer-frame filter admits no state beyond its closure. -/
abbrev FrameFilterReductive (observe : State → Field → Value)
    (gamma : Abs → PSet State) (filter : PSet Field → Abs → Abs)
    (W : PSet Field) (consumerInput : Abs) : Prop :=
  subset (gamma (filter (outside W) consumerInput))
    (projClose observe (outside W) (gamma consumerInput))

abbrev MeetSound (gamma : Abs → PSet State)
    (meet : Abs → Abs → Abs) : Prop :=
  ∀ S₁ S₂, subset (inter (gamma S₁) (gamma S₂)) (gamma (meet S₁ S₂))

abbrev MeetReductive (gamma : Abs → PSet State)
    (meet : Abs → Abs → Abs) : Prop :=
  ∀ S₁ S₂, subset (gamma (meet S₁ S₂)) (inter (gamma S₁) (gamma S₂))

/-- Proposition 5. The nested conjuncts are precision relative to coarse reuse
and actual preservation of the consumer frame. -/
theorem sound_and_precise_frame_preserving_reuse
    (step : State → State → Prop) (observe : State → Field → Value)
    (gamma : Abs → PSet State) (filter : PSet Field → Abs → Abs)
    (meet : Abs → Abs → Abs) (W : PSet Field)
    (storedOutput consumerInput : Abs)
    (hFilterSound : FilterSound observe gamma filter)
    (hCoarseSound : SoundReuse step gamma consumerInput storedOutput)
    (hWriteFrame : WriteFrame step observe W)
    (hFrameFilterReductive :
      FrameFilterReductive observe gamma filter W consumerInput)
    (hMeetSound : MeetSound gamma meet)
    (hMeetReductive : MeetReductive gamma meet) :
    Conj
      (SoundReuse step gamma consumerInput
        (meet storedOutput (filter (outside W) consumerInput)))
      (Conj
        (subset
          (gamma (meet storedOutput (filter (outside W) consumerInput)))
          (gamma storedOutput))
        (subset
          (gamma (meet storedOutput (filter (outside W) consumerInput)))
          (projClose observe (outside W) (gamma consumerInput)))) :=
  Conj.intro
    (fun o ho =>
      have hoStored : gamma storedOutput o := hCoarseSound o ho
      Ex.eliminate ho (fun i hboth =>
        have hoFrame : gamma (filter (outside W) consumerInput) o :=
          hFilterSound (outside W) consumerInput o
            (Ex.intro i
              (Conj.intro (Conj.first hboth)
                (hWriteFrame i o (Conj.second hboth))))
        hMeetSound storedOutput (filter (outside W) consumerInput) o
          (Conj.intro hoStored hoFrame)))
    (Conj.intro
      (fun x hx =>
        Conj.first
          (hMeetReductive storedOutput (filter (outside W) consumerInput) x hx))
      (fun x hx =>
        hFrameFilterReductive x
          (Conj.second
            (hMeetReductive storedOutput
              (filter (outside W) consumerInput) x hx))))

/-- The four propositions assembled into the final end-to-end theorem. -/
theorem end_to_end_sound_summary_reuse
    (step : State → State → Prop) (observe : State → Field → Value)
    (gamma : Abs → PSet State) (relate : PSet Field → Abs → PSet Field)
    (filter : PSet Field → Abs → Abs) (analyze : Abs → Abs)
    (R W A : PSet Field) (producerInput consumerInput : Abs)
    (hRW : ReadWriteExpansion step observe R W)
    (hClosure : ReplayClosure relate R A producerInput)
    (hClosedExact : ClosedExact observe gamma relate filter)
    (hFilterSound : FilterSound observe gamma filter)
    (hAnalyzeSound : AnalyzeSound step gamma analyze)
    (hLookup : Lookup filter A (filter A producerInput) consumerInput) :
    SoundReuse step gamma consumerInput
      (filter (union A W) (analyze producerInput)) :=
  sound_summary_reuse step observe gamma filter A
    (filter A producerInput) (filter (union A W) (analyze producerInput))
    consumerInput hFilterSound
    (summary_soundness step observe gamma relate filter analyze
      R W A producerInput hRW hClosure hClosedExact hFilterSound hAnalyzeSound)
    hLookup

/-- The complete P1--P5 chain. -/
theorem end_to_end_sound_frame_preserving_reuse
    (step : State → State → Prop) (observe : State → Field → Value)
    (gamma : Abs → PSet State) (relate : PSet Field → Abs → PSet Field)
    (filter : PSet Field → Abs → Abs) (analyze : Abs → Abs)
    (meet : Abs → Abs → Abs) (R W A : PSet Field)
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
    Conj
      (SoundReuse step gamma consumerInput
        (meet (filter (union A W) (analyze producerInput))
          (filter (outside W) consumerInput)))
      (Conj
        (subset
          (gamma (meet (filter (union A W) (analyze producerInput))
            (filter (outside W) consumerInput)))
          (gamma (filter (union A W) (analyze producerInput))))
        (subset
          (gamma (meet (filter (union A W) (analyze producerInput))
            (filter (outside W) consumerInput)))
          (projClose observe (outside W) (gamma consumerInput)))) :=
  sound_and_precise_frame_preserving_reuse step observe gamma filter meet W
    (filter (union A W) (analyze producerInput)) consumerInput hFilterSound
    (end_to_end_sound_summary_reuse step observe gamma relate filter analyze
      R W A producerInput consumerInput hRW hClosure hClosedExact
      hFilterSound hAnalyzeSound hLookup)
    hWriteFrame hFrameFilterReductive hMeetSound hMeetReductive

end CompactSoundSummaryCore
