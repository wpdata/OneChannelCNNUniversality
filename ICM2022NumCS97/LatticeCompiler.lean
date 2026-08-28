import ICM2022NumCS97.Universal
import ICM2022NumCS97.GridMachine

/-!
# Compiling affine lattice expressions to the grid machine

Every affine leaf receives one fresh register.  A binary `min` or `max`
receives two additional registers: one for `relu(left - right)` and one for
the result.  The identities

`min(a,b) = a - relu(a-b)` and
`max(a,b) = b + relu(a-b)`

therefore compile the Stone--Weierstrass lattice expressions using only the
verified route, translate, and ReLU instructions.
-/

namespace ICM2022NumCS97

theorem circuitNodeSite_injective {d₁ d₂ : ℕ} :
    Function.Injective (circuitNodeSite d₁ d₂) := by
  intro a b h
  have hrow := congrArg Prod.fst h
  unfold circuitNodeSite gridSite at hrow
  omega

@[simp] theorem circuitNodeSite_inj_iff {d₁ d₂ a b : ℕ} :
    circuitNodeSite d₁ d₂ a = circuitNodeSite d₁ d₂ b ↔ a = b :=
  (circuitNodeSite_injective.eq_iff)

theorem masterGridSite_ne_circuitNode {d₁ d₂ : ℕ}
    (i : Fin d₁) (j : Fin d₂) (t : ℕ) :
    gridSite d₁ d₂ i j ≠ circuitNodeSite d₁ d₂ t := by
  intro h
  have hrow := congrArg Prod.fst h
  unfold circuitNodeSite gridSite at hrow
  have hi := i.isLt
  omega

noncomputable def allMasterEntries (d₁ d₂ : ℕ) :
    List (Fin d₁ × Fin d₂) :=
  (Finset.univ : Finset (Fin d₁ × Fin d₂)).toList

def masterListSum {d₁ d₂ : ℕ}
    (weight : Image d₁ d₂) (value : Site → ℝ)
    (entries : List (Fin d₁ × Fin d₂)) : ℝ :=
  (entries.map fun entry ↦
    weight entry.1 entry.2 *
      value (gridSite d₁ d₂ entry.1 entry.2)).sum

noncomputable def routeMastersToNodeCommands {d₁ d₂ : ℕ}
    (weight : Image d₁ d₂) (target : ℕ) :
    List (Fin d₁ × Fin d₂) → List (GridCommand d₁ d₂)
  | [] => []
  | entry :: tail =>
      .route entry.1 entry.2 (d₁ + target) (d₂ + target)
        (by have := entry.1.isLt; omega)
        (by have := entry.2.isLt; omega)
        (weight entry.1 entry.2) ::
      routeMastersToNodeCommands weight target tail

theorem masterListSum_accumulateNode {d₁ d₂ : ℕ}
    (weight : Image d₁ d₂) (value : Site → ℝ)
    (target : ℕ) (amount : ℝ)
    (entries : List (Fin d₁ × Fin d₂)) :
    masterListSum weight
        (accumulateAt value (circuitNodeSite d₁ d₂ target) amount) entries =
      masterListSum weight value entries := by
  induction entries with
  | nil => rfl
  | cons entry tail ih =>
      simp only [masterListSum, List.map_cons, List.sum_cons]
      change
        (tail.map fun entry ↦
          weight entry.1 entry.2 *
            accumulateAt value (circuitNodeSite d₁ d₂ target) amount
              (gridSite d₁ d₂ entry.1 entry.2)).sum =
          (tail.map fun entry ↦
            weight entry.1 entry.2 *
              value (gridSite d₁ d₂ entry.1 entry.2)).sum at ih
      rw [ih]
      have hne : masterSite d₁ d₂ entry.1 entry.2 ≠
          circuitNodeSite d₁ d₂ target := by
        simpa using
          (masterGridSite_ne_circuitNode entry.1 entry.2 target)
      have hvalue :
          accumulateAt value (circuitNodeSite d₁ d₂ target) amount
              (gridSite d₁ d₂ entry.1 entry.2) =
            value (gridSite d₁ d₂ entry.1 entry.2) := by
        change updateAt value (circuitNodeSite d₁ d₂ target)
            (value (circuitNodeSite d₁ d₂ target) + amount)
            (masterSite d₁ d₂ entry.1 entry.2) = _
        exact updateAt_of_ne value (circuitNodeSite d₁ d₂ target)
          (masterSite d₁ d₂ entry.1 entry.2)
          (value (circuitNodeSite d₁ d₂ target) + amount) hne
      rw [hvalue]

theorem executeGridCommands_routeMastersToNode {d₁ d₂ : ℕ}
    (weight : Image d₁ d₂) (target : ℕ)
    (entries : List (Fin d₁ × Fin d₂)) (value : Site → ℝ) :
    executeGridCommands (routeMastersToNodeCommands weight target entries) value =
      accumulateAt value (circuitNodeSite d₁ d₂ target)
        (masterListSum weight value entries) := by
  induction entries generalizing value with
  | nil =>
      simp only [routeMastersToNodeCommands, executeGridCommands,
        masterListSum, List.map_nil, List.sum_nil]
      rw [accumulateAt_zero]
  | cons entry tail ih =>
      simp only [routeMastersToNodeCommands, executeGridCommands]
      let term := weight entry.1 entry.2 *
        value (gridSite d₁ d₂ entry.1 entry.2)
      change executeGridCommands (routeMastersToNodeCommands weight target tail)
          (accumulateAt value (circuitNodeSite d₁ d₂ target) term) = _
      rw [ih, masterListSum_accumulateNode]
      rw [accumulateAt_accumulateAt]
      simp only [masterListSum, List.map_cons, List.sum_cons]
      rfl

theorem masterListSum_allMasterEntries {d₁ d₂ : ℕ}
    (weight : Image d₁ d₂) (value : Site → ℝ) :
    masterListSum weight value (allMasterEntries d₁ d₂) =
      ∑ i : Fin d₁, ∑ j : Fin d₂,
        weight i j * value (gridSite d₁ d₂ i j) := by
  classical
  simp [masterListSum, allMasterEntries, Fintype.sum_prod_type]

def nodeRouteCommand {d₁ d₂ : ℕ} (source destination : ℕ)
    (h : source < destination) (coefficient : ℝ) : GridCommand d₁ d₂ :=
  .route (d₁ + source) (d₂ + source)
    (d₁ + destination) (d₂ + destination)
    (by omega) (by omega) coefficient

def activateNodeCommand {d₁ d₂ : ℕ} (target : ℕ)
    (mode : ActivationMode) : GridCommand d₁ d₂ :=
  .activate (d₁ + target) (d₂ + target) mode

@[simp] theorem nodeRouteCommand_evalValue {d₁ d₂ source destination : ℕ}
    (h : source < destination) (coefficient : ℝ) (value : Site → ℝ) :
    (nodeRouteCommand (d₁ := d₁) (d₂ := d₂) source destination h
      coefficient).evalValue value =
      accumulateAt value (circuitNodeSite d₁ d₂ destination)
        (coefficient * value (circuitNodeSite d₁ d₂ source)) := rfl

@[simp] theorem activateNodeCommand_evalValue {d₁ d₂ target : ℕ}
    (mode : ActivationMode) (value : Site → ℝ) :
    (activateNodeCommand (d₁ := d₁) (d₂ := d₂) target mode).evalValue value =
      updateAt value (circuitNodeSite d₁ d₂ target)
        (mode.eval (value (circuitNodeSite d₁ d₂ target))) := rfl

def minGateCommands {d₁ d₂ : ℕ} (left right temporary result : ℕ)
    (hleft : left < temporary) (hright : right < temporary)
    (htemporary : temporary < result) : List (GridCommand d₁ d₂) :=
  [nodeRouteCommand left temporary hleft 1,
   nodeRouteCommand right temporary hright (-1),
   activateNodeCommand temporary (.relu 0),
   nodeRouteCommand left result (hleft.trans htemporary) 1,
   nodeRouteCommand temporary result htemporary (-1)]

def maxGateCommands {d₁ d₂ : ℕ} (left right temporary result : ℕ)
    (hleft : left < temporary) (hright : right < temporary)
    (htemporary : temporary < result) : List (GridCommand d₁ d₂) :=
  [nodeRouteCommand left temporary hleft 1,
   nodeRouteCommand right temporary hright (-1),
   activateNodeCommand temporary (.relu 0),
   nodeRouteCommand right result (hright.trans htemporary) 1,
   nodeRouteCommand temporary result htemporary 1]

theorem sub_relu_sub_eq_min (a b : ℝ) : a - relu (a - b) = min a b := by
  by_cases h : a ≤ b
  · have hsub : a - b ≤ 0 := sub_nonpos.mpr h
    rw [relu_of_nonpos hsub, min_eq_left h]
    ring
  · have hba : b ≤ a := le_of_not_ge h
    have hsub : 0 ≤ a - b := sub_nonneg.mpr hba
    rw [relu_of_nonneg hsub, min_eq_right hba]
    ring

theorem add_relu_sub_eq_max (a b : ℝ) : b + relu (a - b) = max a b := by
  by_cases h : a ≤ b
  · have hsub : a - b ≤ 0 := sub_nonpos.mpr h
    rw [relu_of_nonpos hsub, max_eq_right h]
    ring
  · have hba : b ≤ a := le_of_not_ge h
    have hsub : 0 ≤ a - b := sub_nonneg.mpr hba
    rw [relu_of_nonneg hsub, max_eq_left hba]
    ring

theorem executeGridCommands_minGate_result {d₁ d₂ : ℕ}
    {left right temporary result : ℕ}
    (hleft : left < temporary) (hright : right < temporary)
    (htemporary : temporary < result) (value : Site → ℝ)
    (htempZero : value (circuitNodeSite d₁ d₂ temporary) = 0)
    (hresultZero : value (circuitNodeSite d₁ d₂ result) = 0) :
    executeGridCommands
        (minGateCommands (d₁ := d₁) (d₂ := d₂) left right temporary result
          hleft hright htemporary) value
        (circuitNodeSite d₁ d₂ result) =
      min (value (circuitNodeSite d₁ d₂ left))
        (value (circuitNodeSite d₁ d₂ right)) := by
  simp only [minGateCommands, executeGridCommands,
    nodeRouteCommand_evalValue, activateNodeCommand_evalValue]
  simp [accumulateAt, updateAt, circuitNodeSite_inj_iff, hleft.ne,
    hright.ne, htemporary.ne, htemporary.ne', htempZero, hresultZero,
    ActivationMode.eval]
  rw [← relu_eq_max]
  convert sub_relu_sub_eq_min
    (value (circuitNodeSite d₁ d₂ left))
    (value (circuitNodeSite d₁ d₂ right)) using 1 <;> ring

theorem executeGridCommands_maxGate_result {d₁ d₂ : ℕ}
    {left right temporary result : ℕ}
    (hleft : left < temporary) (hright : right < temporary)
    (htemporary : temporary < result) (value : Site → ℝ)
    (htempZero : value (circuitNodeSite d₁ d₂ temporary) = 0)
    (hresultZero : value (circuitNodeSite d₁ d₂ result) = 0) :
    executeGridCommands
        (maxGateCommands (d₁ := d₁) (d₂ := d₂) left right temporary result
          hleft hright htemporary) value
        (circuitNodeSite d₁ d₂ result) =
      max (value (circuitNodeSite d₁ d₂ left))
        (value (circuitNodeSite d₁ d₂ right)) := by
  simp only [maxGateCommands, executeGridCommands,
    nodeRouteCommand_evalValue, activateNodeCommand_evalValue]
  simp [accumulateAt, updateAt, circuitNodeSite_inj_iff, hleft.ne,
    hright.ne, htemporary.ne, htemporary.ne', htempZero, hresultZero,
    ActivationMode.eval]
  rw [← relu_eq_max]
  convert add_relu_sub_eq_max
    (value (circuitNodeSite d₁ d₂ left))
    (value (circuitNodeSite d₁ d₂ right)) using 1 <;> ring

theorem executeGridCommands_minGate_of_ne {d₁ d₂ : ℕ}
    {left right temporary result : ℕ}
    (hleft : left < temporary) (hright : right < temporary)
    (htemporary : temporary < result) (value : Site → ℝ) (s : Site)
    (htemp : s ≠ circuitNodeSite d₁ d₂ temporary)
    (hresult : s ≠ circuitNodeSite d₁ d₂ result) :
    executeGridCommands
        (minGateCommands (d₁ := d₁) (d₂ := d₂) left right temporary result
          hleft hright htemporary) value s = value s := by
  simp [minGateCommands, executeGridCommands, accumulateAt, updateAt,
    htemp, hresult]

theorem executeGridCommands_maxGate_of_ne {d₁ d₂ : ℕ}
    {left right temporary result : ℕ}
    (hleft : left < temporary) (hright : right < temporary)
    (htemporary : temporary < result) (value : Site → ℝ) (s : Site)
    (htemp : s ≠ circuitNodeSite d₁ d₂ temporary)
    (hresult : s ≠ circuitNodeSite d₁ d₂ result) :
    executeGridCommands
        (maxGateCommands (d₁ := d₁) (d₂ := d₂) left right temporary result
          hleft hright htemporary) value s = value s := by
  simp [maxGateCommands, executeGridCommands, accumulateAt, updateAt,
    htemp, hresult]

theorem executeGridCommands_append {d₁ d₂ : ℕ}
    (first second : List (GridCommand d₁ d₂)) (value : Site → ℝ) :
    executeGridCommands (first ++ second) value =
      executeGridCommands second (executeGridCommands first value) := by
  induction first generalizing value with
  | nil => rfl
  | cons command tail ih =>
      simp only [List.cons_append, executeGridCommands]
      exact ih (command.evalValue value)

theorem executeGridCommands_affineNode {d₁ d₂ : ℕ}
    (weight : Image d₁ d₂) (constant : ℝ) (target : ℕ)
    (value : Site → ℝ) :
    executeGridCommands
        (routeMastersToNodeCommands weight target (allMasterEntries d₁ d₂) ++
          [activateNodeCommand target (.translate constant)]) value =
      updateAt value (circuitNodeSite d₁ d₂ target)
        (value (circuitNodeSite d₁ d₂ target) +
          masterListSum weight value (allMasterEntries d₁ d₂) + constant) := by
  rw [executeGridCommands_append,
    executeGridCommands_routeMastersToNode]
  simp only [executeGridCommands, activateNodeCommand_evalValue,
    ActivationMode.eval]
  funext s
  by_cases hs : s = circuitNodeSite d₁ d₂ target
  · subst s
    simp [accumulateAt, updateAt]
  · simp [accumulateAt, updateAt, hs]

namespace LatticeExpr

def nodeCount {d₁ d₂ : ℕ} : LatticeExpr d₁ d₂ → ℕ
  | .affine _ _ => 1
  | .min left right => left.nodeCount + right.nodeCount + 2
  | .max left right => left.nodeCount + right.nodeCount + 2

theorem nodeCount_pos {d₁ d₂ : ℕ} (e : LatticeExpr d₁ d₂) :
    0 < e.nodeCount := by
  cases e <;> simp [nodeCount] <;> omega

def outputIndex {d₁ d₂ : ℕ} (e : LatticeExpr d₁ d₂) (start : ℕ) : ℕ :=
  start + e.nodeCount - 1

theorem outputIndex_lt_end {d₁ d₂ : ℕ}
    (e : LatticeExpr d₁ d₂) (start : ℕ) :
    e.outputIndex start < start + e.nodeCount := by
  unfold outputIndex
  have := e.nodeCount_pos
  omega

theorem start_le_outputIndex {d₁ d₂ : ℕ}
    (e : LatticeExpr d₁ d₂) (start : ℕ) :
    start ≤ e.outputIndex start := by
  unfold outputIndex
  have := e.nodeCount_pos
  omega

noncomputable def compileCommands {d₁ d₂ : ℕ} :
    (e : LatticeExpr d₁ d₂) → ℕ → List (GridCommand d₁ d₂)
  | .affine weight constant, start =>
      routeMastersToNodeCommands weight start (allMasterEntries d₁ d₂) ++
        [activateNodeCommand start (.translate constant)]
  | .min left right, start =>
      let rightStart := start + left.nodeCount
      let temporary := rightStart + right.nodeCount
      let result := temporary + 1
      left.compileCommands start ++
        (right.compileCommands rightStart ++
          minGateCommands (left.outputIndex start)
            (right.outputIndex rightStart) temporary result
            (by
              have hl := left.outputIndex_lt_end start
              omega)
            (by
              have hr := right.outputIndex_lt_end rightStart
              omega)
            (by omega))
  | .max left right, start =>
      let rightStart := start + left.nodeCount
      let temporary := rightStart + right.nodeCount
      let result := temporary + 1
      left.compileCommands start ++
        (right.compileCommands rightStart ++
          maxGateCommands (left.outputIndex start)
            (right.outputIndex rightStart) temporary result
            (by
              have hl := left.outputIndex_lt_end start
              omega)
            (by
              have hr := right.outputIndex_lt_end rightStart
              omega)
            (by omega))

/-- Strong compiler invariant.  Besides the output equation, it records that
all input masters and all node registers outside the freshly allocated block
are unchanged. -/
structure CompileSpec {d₁ d₂ : ℕ} (e : LatticeExpr d₁ d₂) (start : ℕ)
    (value : Site → ℝ) (x : Image d₁ d₂) (result : Site → ℝ) : Prop where
  output_eq :
    result (circuitNodeSite d₁ d₂ (e.outputIndex start)) = e.evalEncoded x
  master_eq : ∀ i : Fin d₁, ∀ j : Fin d₂,
    result (gridSite d₁ d₂ i j) = value (gridSite d₁ d₂ i j)
  before_eq : ∀ t, t < start →
    result (circuitNodeSite d₁ d₂ t) = value (circuitNodeSite d₁ d₂ t)
  after_eq : ∀ t, start + e.nodeCount ≤ t →
    result (circuitNodeSite d₁ d₂ t) = value (circuitNodeSite d₁ d₂ t)

/-- Semantic correctness and freshness preservation for the complete
lattice-expression compiler. -/
theorem compileCommands_spec {d₁ d₂ : ℕ} (e : LatticeExpr d₁ d₂)
    (start : ℕ) (x : Image d₁ d₂) (value : Site → ℝ)
    (hmaster : ∀ i : Fin d₁, ∀ j : Fin d₂,
      value (gridSite d₁ d₂ i j) = sparseEncodedValue x i j)
    (hfresh : ∀ t, start ≤ t →
      value (circuitNodeSite d₁ d₂ t) = 0) :
    CompileSpec e start value x
      (executeGridCommands (e.compileCommands start) value) := by
  induction e generalizing start value with
  | affine weight constant =>
      have hrun := executeGridCommands_affineNode weight constant start value
      constructor
      · simp only [compileCommands, outputIndex, nodeCount]
        rw [hrun]
        have hidx : start + 1 - 1 = start := by omega
        rw [hidx, updateAt_same]
        rw [hfresh start (le_refl start), zero_add]
        rw [masterListSum_allMasterEntries]
        simp_rw [hmaster]
        rfl
      · intro i j
        simp only [compileCommands]
        rw [hrun]
        apply updateAt_of_ne
        exact masterGridSite_ne_circuitNode i j start
      · intro t ht
        simp only [compileCommands]
        rw [hrun]
        apply updateAt_of_ne
        intro h
        have := circuitNodeSite_injective h
        omega
      · intro t ht
        simp only [compileCommands]
        rw [hrun]
        apply updateAt_of_ne
        intro h
        have := circuitNodeSite_injective h
        simp only [nodeCount] at ht
        omega
  | min left right ihleft ihrigh =>
      let rightStart := start + left.nodeCount
      let temporary := rightStart + right.nodeCount
      let resultIndex := temporary + 1
      have hleftTemp : left.outputIndex start < temporary := by
        have h := left.outputIndex_lt_end start
        have hr := right.nodeCount_pos
        dsimp [temporary, rightStart]
        omega
      have hrightTemp : right.outputIndex rightStart < temporary := by
        have h := right.outputIndex_lt_end rightStart
        dsimp [temporary]
        exact h
      have htempResult : temporary < resultIndex := by
        dsimp [resultIndex]
        omega
      let leftValue := executeGridCommands (left.compileCommands start) value
      have hleftSpec : CompileSpec left start value x leftValue :=
        ihleft start value hmaster hfresh
      have hmasterRight : ∀ i : Fin d₁, ∀ j : Fin d₂,
          leftValue (gridSite d₁ d₂ i j) = sparseEncodedValue x i j := by
        intro i j
        rw [hleftSpec.master_eq, hmaster]
      have hfreshRight : ∀ t, rightStart ≤ t →
          leftValue (circuitNodeSite d₁ d₂ t) = 0 := by
        intro t ht
        rw [hleftSpec.after_eq t (by
          dsimp [rightStart] at ht ⊢
          exact ht)]
        exact hfresh t (by
          dsimp [rightStart] at ht
          omega)
      let rightValue :=
        executeGridCommands (right.compileCommands rightStart) leftValue
      have hrightSpec : CompileSpec right rightStart leftValue x rightValue :=
        ihrigh rightStart leftValue hmasterRight hfreshRight
      let gate := minGateCommands (d₁ := d₁) (d₂ := d₂)
        (left.outputIndex start) (right.outputIndex rightStart)
        temporary resultIndex hleftTemp hrightTemp htempResult
      let finalValue := executeGridCommands gate rightValue
      have hcompiled :
          executeGridCommands ((LatticeExpr.min left right).compileCommands start)
              value = finalValue := by
        simp only [compileCommands, executeGridCommands_append]
        rfl
      have hleftInRight :
          rightValue (circuitNodeSite d₁ d₂ (left.outputIndex start)) =
            left.evalEncoded x := by
        rw [hrightSpec.before_eq]
        · exact hleftSpec.output_eq
        · have h := left.outputIndex_lt_end start
          dsimp [rightStart]
          exact h
      have hrightValue :
          rightValue (circuitNodeSite d₁ d₂ (right.outputIndex rightStart)) =
            right.evalEncoded x := hrightSpec.output_eq
      have htempZero :
          rightValue (circuitNodeSite d₁ d₂ temporary) = 0 := by
        calc
          rightValue (circuitNodeSite d₁ d₂ temporary) =
              leftValue (circuitNodeSite d₁ d₂ temporary) :=
            hrightSpec.after_eq temporary (by
              dsimp [temporary]
              omega)
          _ = value (circuitNodeSite d₁ d₂ temporary) :=
            hleftSpec.after_eq temporary (by
              dsimp [temporary, rightStart]
              omega)
          _ = 0 := hfresh temporary (by
              dsimp [temporary, rightStart]
              omega)
      have hresultZero :
          rightValue (circuitNodeSite d₁ d₂ resultIndex) = 0 := by
        calc
          rightValue (circuitNodeSite d₁ d₂ resultIndex) =
              leftValue (circuitNodeSite d₁ d₂ resultIndex) :=
            hrightSpec.after_eq resultIndex (by
              dsimp [resultIndex, temporary]
              omega)
          _ = value (circuitNodeSite d₁ d₂ resultIndex) :=
            hleftSpec.after_eq resultIndex (by
              dsimp [resultIndex, temporary, rightStart]
              omega)
          _ = 0 := hfresh resultIndex (by
              dsimp [resultIndex, temporary, rightStart]
              omega)
      have hgateOutput :
          finalValue (circuitNodeSite d₁ d₂ resultIndex) =
            Min.min (left.evalEncoded x) (right.evalEncoded x) := by
        change executeGridCommands gate rightValue
            (circuitNodeSite d₁ d₂ resultIndex) = _
        rw [executeGridCommands_minGate_result hleftTemp hrightTemp
          htempResult rightValue htempZero hresultZero,
          hleftInRight, hrightValue]
      have houtputIndex :
          (LatticeExpr.min left right).outputIndex start = resultIndex := by
        simp only [outputIndex, nodeCount]
        dsimp [resultIndex, temporary, rightStart]
        have hl := left.nodeCount_pos
        have hr := right.nodeCount_pos
        omega
      constructor
      · rw [hcompiled, houtputIndex]
        exact hgateOutput
      · intro i j
        rw [hcompiled]
        calc
          finalValue (gridSite d₁ d₂ i j) =
              rightValue (gridSite d₁ d₂ i j) := by
            apply executeGridCommands_minGate_of_ne hleftTemp hrightTemp
              htempResult rightValue
            · exact masterGridSite_ne_circuitNode i j temporary
            · exact masterGridSite_ne_circuitNode i j resultIndex
          _ = leftValue (gridSite d₁ d₂ i j) :=
            hrightSpec.master_eq i j
          _ = value (gridSite d₁ d₂ i j) := hleftSpec.master_eq i j
      · intro t ht
        rw [hcompiled]
        have hneTemp : circuitNodeSite d₁ d₂ t ≠
            circuitNodeSite d₁ d₂ temporary := by
          intro h
          have heq := circuitNodeSite_injective h
          dsimp [temporary, rightStart] at heq
          omega
        have hneResult : circuitNodeSite d₁ d₂ t ≠
            circuitNodeSite d₁ d₂ resultIndex := by
          intro h
          have heq := circuitNodeSite_injective h
          dsimp [resultIndex, temporary, rightStart] at heq
          omega
        calc
          finalValue (circuitNodeSite d₁ d₂ t) =
              rightValue (circuitNodeSite d₁ d₂ t) :=
            executeGridCommands_minGate_of_ne hleftTemp hrightTemp
              htempResult rightValue _ hneTemp hneResult
          _ = leftValue (circuitNodeSite d₁ d₂ t) :=
            hrightSpec.before_eq t (by
              dsimp [rightStart]
              omega)
          _ = value (circuitNodeSite d₁ d₂ t) :=
            hleftSpec.before_eq t ht
      · intro t ht
        rw [hcompiled]
        have hend : resultIndex < t := by
          simp only [nodeCount] at ht
          dsimp [resultIndex, temporary, rightStart]
          omega
        have hneTemp : circuitNodeSite d₁ d₂ t ≠
            circuitNodeSite d₁ d₂ temporary := by
          intro h
          have heq := circuitNodeSite_injective h
          omega
        have hneResult : circuitNodeSite d₁ d₂ t ≠
            circuitNodeSite d₁ d₂ resultIndex := by
          intro h
          have heq := circuitNodeSite_injective h
          omega
        calc
          finalValue (circuitNodeSite d₁ d₂ t) =
              rightValue (circuitNodeSite d₁ d₂ t) :=
            executeGridCommands_minGate_of_ne hleftTemp hrightTemp
              htempResult rightValue _ hneTemp hneResult
          _ = leftValue (circuitNodeSite d₁ d₂ t) :=
            hrightSpec.after_eq t (by
              dsimp [temporary, rightStart] at hend ⊢
              omega)
          _ = value (circuitNodeSite d₁ d₂ t) :=
            hleftSpec.after_eq t (by omega)
  | max left right ihleft ihrigh =>
      let rightStart := start + left.nodeCount
      let temporary := rightStart + right.nodeCount
      let resultIndex := temporary + 1
      have hleftTemp : left.outputIndex start < temporary := by
        have h := left.outputIndex_lt_end start
        have hr := right.nodeCount_pos
        dsimp [temporary, rightStart]
        omega
      have hrightTemp : right.outputIndex rightStart < temporary := by
        have h := right.outputIndex_lt_end rightStart
        dsimp [temporary]
        exact h
      have htempResult : temporary < resultIndex := by
        dsimp [resultIndex]
        omega
      let leftValue := executeGridCommands (left.compileCommands start) value
      have hleftSpec : CompileSpec left start value x leftValue :=
        ihleft start value hmaster hfresh
      have hmasterRight : ∀ i : Fin d₁, ∀ j : Fin d₂,
          leftValue (gridSite d₁ d₂ i j) = sparseEncodedValue x i j := by
        intro i j
        rw [hleftSpec.master_eq, hmaster]
      have hfreshRight : ∀ t, rightStart ≤ t →
          leftValue (circuitNodeSite d₁ d₂ t) = 0 := by
        intro t ht
        rw [hleftSpec.after_eq t (by
          dsimp [rightStart] at ht ⊢
          exact ht)]
        exact hfresh t (by
          dsimp [rightStart] at ht
          omega)
      let rightValue :=
        executeGridCommands (right.compileCommands rightStart) leftValue
      have hrightSpec : CompileSpec right rightStart leftValue x rightValue :=
        ihrigh rightStart leftValue hmasterRight hfreshRight
      let gate := maxGateCommands (d₁ := d₁) (d₂ := d₂)
        (left.outputIndex start) (right.outputIndex rightStart)
        temporary resultIndex hleftTemp hrightTemp htempResult
      let finalValue := executeGridCommands gate rightValue
      have hcompiled :
          executeGridCommands ((LatticeExpr.max left right).compileCommands start)
              value = finalValue := by
        simp only [compileCommands, executeGridCommands_append]
        rfl
      have hleftInRight :
          rightValue (circuitNodeSite d₁ d₂ (left.outputIndex start)) =
            left.evalEncoded x := by
        rw [hrightSpec.before_eq]
        · exact hleftSpec.output_eq
        · have h := left.outputIndex_lt_end start
          dsimp [rightStart]
          exact h
      have hrightValue :
          rightValue (circuitNodeSite d₁ d₂ (right.outputIndex rightStart)) =
            right.evalEncoded x := hrightSpec.output_eq
      have htempZero :
          rightValue (circuitNodeSite d₁ d₂ temporary) = 0 := by
        calc
          rightValue (circuitNodeSite d₁ d₂ temporary) =
              leftValue (circuitNodeSite d₁ d₂ temporary) :=
            hrightSpec.after_eq temporary (by
              dsimp [temporary]
              omega)
          _ = value (circuitNodeSite d₁ d₂ temporary) :=
            hleftSpec.after_eq temporary (by
              dsimp [temporary, rightStart]
              omega)
          _ = 0 := hfresh temporary (by
              dsimp [temporary, rightStart]
              omega)
      have hresultZero :
          rightValue (circuitNodeSite d₁ d₂ resultIndex) = 0 := by
        calc
          rightValue (circuitNodeSite d₁ d₂ resultIndex) =
              leftValue (circuitNodeSite d₁ d₂ resultIndex) :=
            hrightSpec.after_eq resultIndex (by
              dsimp [resultIndex, temporary]
              omega)
          _ = value (circuitNodeSite d₁ d₂ resultIndex) :=
            hleftSpec.after_eq resultIndex (by
              dsimp [resultIndex, temporary, rightStart]
              omega)
          _ = 0 := hfresh resultIndex (by
              dsimp [resultIndex, temporary, rightStart]
              omega)
      have hgateOutput :
          finalValue (circuitNodeSite d₁ d₂ resultIndex) =
            Max.max (left.evalEncoded x) (right.evalEncoded x) := by
        change executeGridCommands gate rightValue
            (circuitNodeSite d₁ d₂ resultIndex) = _
        rw [executeGridCommands_maxGate_result hleftTemp hrightTemp
          htempResult rightValue htempZero hresultZero,
          hleftInRight, hrightValue]
      have houtputIndex :
          (LatticeExpr.max left right).outputIndex start = resultIndex := by
        simp only [outputIndex, nodeCount]
        dsimp [resultIndex, temporary, rightStart]
        have hl := left.nodeCount_pos
        have hr := right.nodeCount_pos
        omega
      constructor
      · rw [hcompiled, houtputIndex]
        exact hgateOutput
      · intro i j
        rw [hcompiled]
        calc
          finalValue (gridSite d₁ d₂ i j) =
              rightValue (gridSite d₁ d₂ i j) := by
            apply executeGridCommands_maxGate_of_ne hleftTemp hrightTemp
              htempResult rightValue
            · exact masterGridSite_ne_circuitNode i j temporary
            · exact masterGridSite_ne_circuitNode i j resultIndex
          _ = leftValue (gridSite d₁ d₂ i j) :=
            hrightSpec.master_eq i j
          _ = value (gridSite d₁ d₂ i j) := hleftSpec.master_eq i j
      · intro t ht
        rw [hcompiled]
        have hneTemp : circuitNodeSite d₁ d₂ t ≠
            circuitNodeSite d₁ d₂ temporary := by
          intro h
          have heq := circuitNodeSite_injective h
          dsimp [temporary, rightStart] at heq
          omega
        have hneResult : circuitNodeSite d₁ d₂ t ≠
            circuitNodeSite d₁ d₂ resultIndex := by
          intro h
          have heq := circuitNodeSite_injective h
          dsimp [resultIndex, temporary, rightStart] at heq
          omega
        calc
          finalValue (circuitNodeSite d₁ d₂ t) =
              rightValue (circuitNodeSite d₁ d₂ t) :=
            executeGridCommands_maxGate_of_ne hleftTemp hrightTemp
              htempResult rightValue _ hneTemp hneResult
          _ = leftValue (circuitNodeSite d₁ d₂ t) :=
            hrightSpec.before_eq t (by
              dsimp [rightStart]
              omega)
          _ = value (circuitNodeSite d₁ d₂ t) :=
            hleftSpec.before_eq t ht
      · intro t ht
        rw [hcompiled]
        have hend : resultIndex < t := by
          simp only [nodeCount] at ht
          dsimp [resultIndex, temporary, rightStart]
          omega
        have hneTemp : circuitNodeSite d₁ d₂ t ≠
            circuitNodeSite d₁ d₂ temporary := by
          intro h
          have heq := circuitNodeSite_injective h
          omega
        have hneResult : circuitNodeSite d₁ d₂ t ≠
            circuitNodeSite d₁ d₂ resultIndex := by
          intro h
          have heq := circuitNodeSite_injective h
          omega
        calc
          finalValue (circuitNodeSite d₁ d₂ t) =
              rightValue (circuitNodeSite d₁ d₂ t) :=
            executeGridCommands_maxGate_of_ne hleftTemp hrightTemp
              htempResult rightValue _ hneTemp hneResult
          _ = leftValue (circuitNodeSite d₁ d₂ t) :=
            hrightSpec.after_eq t (by
              dsimp [temporary, rightStart] at hend ⊢
              omega)
          _ = value (circuitNodeSite d₁ d₂ t) :=
            hleftSpec.after_eq t (by omega)

theorem compileCommands_output {d₁ d₂ : ℕ} (e : LatticeExpr d₁ d₂)
    (start : ℕ) (x : Image d₁ d₂) (value : Site → ℝ)
    (hmaster : ∀ i : Fin d₁, ∀ j : Fin d₂,
      value (gridSite d₁ d₂ i j) = sparseEncodedValue x i j)
    (hfresh : ∀ t, start ≤ t →
      value (circuitNodeSite d₁ d₂ t) = 0) :
    executeGridCommands (e.compileCommands start) value
        (circuitNodeSite d₁ d₂ (e.outputIndex start)) =
      e.evalEncoded x :=
  (compileCommands_spec e start x value hmaster hfresh).output_eq

end LatticeExpr

end ICM2022NumCS97
