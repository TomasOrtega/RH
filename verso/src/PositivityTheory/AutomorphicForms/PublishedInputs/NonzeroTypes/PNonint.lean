import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace P_nonint

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Set `M : Matrix (Fin n) (Fin n) 𝒪[k]` to `fun i j => ⟨(g : Matrix (Fin n) (Fin n) k) i j, hint i j⟩`. Establish `hdetM : algebraMap 𝒪[k] k M.det = (g : Matrix (Fin n) (Fin n) k).det`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Establish `hu : IsUnit M.det`.

Rewrite using `[(Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one, hdetM, hdet]`. Establish `hU : IsUnit M` using `(Matrix.isUnit_iff_isUnit_det M).2 hu`. Use `⟨hU.unit, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem mem_KO_of {n : ℕ} (g : GL (Fin n) k)
    (hint : ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1)
    (hdet : valuation k (g : Matrix (Fin n) (Fin n) k).det = 1) : g ∈ KO k (Fin n) := by
  let M : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨(g : Matrix (Fin n) (Fin n) k) i j, hint i j⟩
  have hdetM : algebraMap 𝒪[k] k M.det = (g : Matrix (Fin n) (Fin n) k).det := by
    rw [RingHom.map_det]
    rfl
  have hu : IsUnit M.det := by
    rw [(Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one, hdetM, hdet]
  have hU : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 hu
  refine ⟨hU.unit, ?_⟩
  ext i j
  rfl

/- English proof (translation)
Unfold `GlobalTheory.SmGL.unipRad at hY`. Take `⟨P, hP, rfl⟩` from `Subgroup.mem_map.1 hY`. Establish `htri : ((P : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular (GlobalTheory.SmGL.blk G.e)` using `P.2`. Establish `hdiag : ∀ a, GlobalTheory.SmGL.diagBlock k G.e a P = 1`. Introduce `a`.

Establish `h1` using `congrFun (MonoidHom.mem_ker.1 hP) a`. Conclude with `congrArg Units.val h1`. Prove the components needed by the constructor for the conclusion. Introduce `hlt`. Conclude with `htri hlt`.

Introduce `heq`. Take `⟨⟨a, x⟩, rfl⟩` from `G.e.surjective i`. Take `⟨⟨b, y⟩, rfl⟩` from `G.e.surjective j`. Establish `ha : G.bl (G.e ⟨a, x⟩) = a` using `by simp [UpperTheory.TNZ.Grp.bl]`. Establish `hb : G.bl (G.e ⟨b, y⟩) = b` using `by simp [UpperTheory.TNZ.Grp.bl]`.

Rewrite `heq` using `[ha, hb]`. Substitute `heq` using the available equality. Establish `h2` using `congrFun (congrFun (hdiag a) x) y`. Simplify using `only [GlobalTheory.SmGL.diagBlock, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.submatrix_apply, Matrix.one_apply] at h2`. Rewrite using `[Subgroup.coe_subtype, h2]`.

Distinguish the cases in `hxy : x = y`. Substitute `hxy` using the available equality. Simplify using the standard rewrite rules. Establish `hne : G.e ⟨a, x⟩ ≠ G.e ⟨a, y⟩` using `fun e => hxy (by simpa using G.e.injective e)`. Simplify using `[hxy, hne]`.
-/
theorem unip_entry {n : ℕ} (G : Grp k n) {Y : GL (Fin n) k} (hY : Y ∈ unipRad k G.e) (i j : Fin n) :
    (G.bl j < G.bl i → (Y : Matrix (Fin n) (Fin n) k) i j = 0) ∧
      (G.bl i = G.bl j → (Y : Matrix (Fin n) (Fin n) k) i j = if i = j then 1 else 0) := by
  unfold GlobalTheory.SmGL.unipRad at hY
  obtain ⟨P, hP, rfl⟩ := Subgroup.mem_map.1 hY
  have htri : ((P : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular (GlobalTheory.SmGL.blk G.e) := P.2
  have hdiag : ∀ a, GlobalTheory.SmGL.diagBlock k G.e a P = 1 := by
    intro a
    have h1 := congrFun (MonoidHom.mem_ker.1 hP) a
    exact congrArg Units.val h1
  constructor
  · intro hlt
    exact htri hlt
  · intro heq
    obtain ⟨⟨a, x⟩, rfl⟩ := G.e.surjective i
    obtain ⟨⟨b, y⟩, rfl⟩ := G.e.surjective j
    have ha : G.bl (G.e ⟨a, x⟩) = a := by simp [UpperTheory.TNZ.Grp.bl]
    have hb : G.bl (G.e ⟨b, y⟩) = b := by simp [UpperTheory.TNZ.Grp.bl]
    rw [ha, hb] at heq
    subst heq
    have h2 := congrFun (congrFun (hdiag a) x) y
    simp only [GlobalTheory.SmGL.diagBlock, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.submatrix_apply,
      Matrix.one_apply] at h2
    rw [Subgroup.coe_subtype, h2]
    by_cases hxy : x = y
    · subst hxy
      simp
    · have hne : G.e ⟨a, x⟩ ≠ G.e ⟨a, y⟩ := fun e => hxy (by simpa using G.e.injective e)
      simp [hxy, hne]

/- English proof (translation)
Assume the negation of the conclusion as `hnone`. Use `push Not at hnone`. Apply `hK` to reduce the goal to its premises. Apply the tactic sequence `have htri : (Y : Matrix (Fin n) (Fin n) k).BlockTriangular G.bl := fun i j h => (unip_entry G hY i j).1 h`. Establish `hdet1 : (Y : Matrix (Fin n) (Fin n) k).det = 1`.

Rewrite using `[htri.det]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `a _`. Establish `e1 : (Y : Matrix (Fin n) (Fin n) k).toSquareBlock G.bl a = 1`. Use extensionality with `x y`.

Apply the tactic sequence `rw [Matrix.toSquareBlock_def, Matrix.of_apply, (unip_entry G hY x y).2 (x.2.trans y.2.symm)]`. Simplify using `[Matrix.one_apply, Subtype.ext_iff]`. Rewrite using `[e1, Matrix.det_one]`. Conclude with `mem_KO_of Y hnone (by rw [hdet1, map_one])`.
-/
theorem exists_big {n : ℕ} (G : Grp k n) {Y : GL (Fin n) k} (hY : Y ∈ unipRad k G.e)
    (hK : Y ∉ KO k (Fin n)) : ∃ i j, 1 < valuation k ((Y : Matrix (Fin n) (Fin n) k) i j) := by
  by_contra hnone
  push Not at hnone
  apply hK
  have htri : (Y : Matrix (Fin n) (Fin n) k).BlockTriangular G.bl := fun i j h => (unip_entry G hY i j).1 h
  have hdet1 : (Y : Matrix (Fin n) (Fin n) k).det = 1 := by
    rw [htri.det]
    apply Finset.prod_eq_one
    intro a _
    have e1 : (Y : Matrix (Fin n) (Fin n) k).toSquareBlock G.bl a = 1 := by
      ext x y
      rw [Matrix.toSquareBlock_def, Matrix.of_apply, (unip_entry G hY x y).2 (x.2.trans y.2.symm)]
      simp [Matrix.one_apply, Subtype.ext_iff]
    rw [e1, Matrix.det_one]
  exact mem_KO_of Y hnone (by rw [hdet1, map_one])

/- English proof (translation)
Take `⟨i1, j1, h1⟩` from `hbig`. Establish `hsmall : ∀ i j, ¬ G.bl i < G.bl j → valuation k ((Y : Matrix (Fin n) (Fin n) k) i j) ≤ 1`. Introduce `i j hij`. Break down `lt_or_eq_of_le (not_lt.mp hij) with h | h` into its components or cases. Apply the tactic sequence `rw [(unip_entry G hY i j).1 h, map_zero]`.

Conclude with `zero_le`. Apply the tactic sequence `rw [(unip_entry G hY i j).2 h.symm] split_ifs <;> simp`. Take `⟨x0, -, hx0⟩` from `Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n)) (fun x => valuation k ((Y : Matrix (Fin n) (Fin n) k) x.1 x.2)) ⟨(i1, j1), Finset.mem_univ _⟩`. Take `⟨⟨p, q⟩, hpqT, hmin⟩` from `Finset.exists_min_image ((Finset.univ : Finset (Fin n × Fin n)).filter (fun x => valuation k ((Y : Matrix (Fin n) (Fin n) k) x.1 x.2) = valuation k ((Y : Matrix (Fin n) (Fin n) k) x0.1 x0.2))) (fun x => (G.bl x.2 : ℕ) - (G.bl x.1 : ℕ)) ⟨x0, by simp⟩`. Establish `hpq : valuation k ((Y : Matrix (Fin n) (Fin n) k) p q) = valuation k ((Y : Matrix (Fin n) (Fin n) k) x0.1 x0.2)`.

Simplify using `using hpqT`. Establish `hle : ∀ i j, valuation k ((Y : Matrix (Fin n) (Fin n) k) i j) ≤ valuation k ((Y : Matrix (Fin n) (Fin n) k) p q)`. Introduce `i j`. Rewrite using `[hpq]`. Conclude with `hx0 (i, j) (Finset.mem_univ _)`.

Establish `hgt : 1 < valuation k ((Y : Matrix (Fin n) (Fin n) k) p q)` using `lt_of_lt_of_le h1 (hle i1 j1)`. Establish `hlt : G.bl p < G.bl q`. Assume the negation of the conclusion as `h`. Conclude with `absurd (hsmall p q h) (not_le.mpr hgt)`. Use `⟨p, q, hlt, fun i => hle p i, fun i => hle i q, fun i hi => ?_, fun i hi => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Establish `heq : valuation k ((Y : Matrix (Fin n) (Fin n) k) p i) = valuation k ((Y : Matrix (Fin n) (Fin n) k) p q)` using `le_antisymm (hle p i) (not_lt.mp hne)`. Distinguish the cases in `hpi : G.bl p < G.bl i`. Use `hmin (p, i) (by simp [heq, hpq])` as an intermediate fact. Establish `h1'` using `Fin.lt_def.mp hpi`.

Establish `h2'` using `Fin.lt_def.mp hi`. Simplify using `only at this`. Use linear arithmetic over natural numbers and integers. Use `hsmall p i hpi` as an intermediate fact. Rewrite `this` using `[heq]`.

Conclude with `absurd this (not_le.mpr hgt)`. Assume the negation of the conclusion as `hne`. Establish `heq : valuation k ((Y : Matrix (Fin n) (Fin n) k) i q) = valuation k ((Y : Matrix (Fin n) (Fin n) k) p q)` using `le_antisymm (hle i q) (not_lt.mp hne)`. Distinguish the cases in `hiq : G.bl i < G.bl q`. Use `hmin (i, q) (by simp [heq, hpq])` as an intermediate fact.

Establish `h1'` using `Fin.lt_def.mp hi`. Establish `h2'` using `Fin.lt_def.mp hiq`. Simplify using `only at this`. Use linear arithmetic over natural numbers and integers. Use `hsmall i q hiq` as an intermediate fact.

Rewrite `this` using `[heq]`. Conclude with `absurd this (not_le.mpr hgt)`.
-/
theorem select {n : ℕ} (G : Grp k n) {Y : GL (Fin n) k} (hY : Y ∈ unipRad k G.e)
    (hbig : ∃ i j, 1 < valuation k ((Y : Matrix (Fin n) (Fin n) k) i j)) :
    ∃ p q, G.bl p < G.bl q ∧
      (∀ i, valuation k ((Y : Matrix (Fin n) (Fin n) k) p i) ≤ valuation k ((Y : Matrix (Fin n) (Fin n) k) p q)) ∧
      (∀ i, valuation k ((Y : Matrix (Fin n) (Fin n) k) i q) ≤ valuation k ((Y : Matrix (Fin n) (Fin n) k) p q)) ∧
      (∀ i, G.bl i < G.bl q →
        valuation k ((Y : Matrix (Fin n) (Fin n) k) p i) < valuation k ((Y : Matrix (Fin n) (Fin n) k) p q)) ∧
      (∀ i, G.bl p < G.bl i →
        valuation k ((Y : Matrix (Fin n) (Fin n) k) i q) < valuation k ((Y : Matrix (Fin n) (Fin n) k) p q)) := by
  obtain ⟨i1, j1, h1⟩ := hbig
  have hsmall : ∀ i j, ¬ G.bl i < G.bl j → valuation k ((Y : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
    intro i j hij
    rcases lt_or_eq_of_le (not_lt.mp hij) with h | h
    · rw [(unip_entry G hY i j).1 h, map_zero]
      exact zero_le
    · rw [(unip_entry G hY i j).2 h.symm]
      split_ifs <;> simp
  obtain ⟨x0, -, hx0⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
    (fun x => valuation k ((Y : Matrix (Fin n) (Fin n) k) x.1 x.2)) ⟨(i1, j1), Finset.mem_univ _⟩
  obtain ⟨⟨p, q⟩, hpqT, hmin⟩ := Finset.exists_min_image
    ((Finset.univ : Finset (Fin n × Fin n)).filter (fun x => valuation k ((Y : Matrix (Fin n) (Fin n) k) x.1 x.2) =
      valuation k ((Y : Matrix (Fin n) (Fin n) k) x0.1 x0.2)))
    (fun x => (G.bl x.2 : ℕ) - (G.bl x.1 : ℕ)) ⟨x0, by simp⟩
  have hpq : valuation k ((Y : Matrix (Fin n) (Fin n) k) p q) =
      valuation k ((Y : Matrix (Fin n) (Fin n) k) x0.1 x0.2) := by
    simpa using hpqT
  have hle : ∀ i j, valuation k ((Y : Matrix (Fin n) (Fin n) k) i j) ≤
      valuation k ((Y : Matrix (Fin n) (Fin n) k) p q) := by
    intro i j
    rw [hpq]
    exact hx0 (i, j) (Finset.mem_univ _)
  have hgt : 1 < valuation k ((Y : Matrix (Fin n) (Fin n) k) p q) := lt_of_lt_of_le h1 (hle i1 j1)
  have hlt : G.bl p < G.bl q := by
    by_contra h
    exact absurd (hsmall p q h) (not_le.mpr hgt)
  refine ⟨p, q, hlt, fun i => hle p i, fun i => hle i q, fun i hi => ?_, fun i hi => ?_⟩
  · by_contra hne
    have heq : valuation k ((Y : Matrix (Fin n) (Fin n) k) p i) =
        valuation k ((Y : Matrix (Fin n) (Fin n) k) p q) := le_antisymm (hle p i) (not_lt.mp hne)
    by_cases hpi : G.bl p < G.bl i
    · have := hmin (p, i) (by simp [heq, hpq])
      have h1' := Fin.lt_def.mp hpi
      have h2' := Fin.lt_def.mp hi
      simp only at this
      omega
    · have := hsmall p i hpi
      rw [heq] at this
      exact absurd this (not_le.mpr hgt)
  · by_contra hne
    have heq : valuation k ((Y : Matrix (Fin n) (Fin n) k) i q) =
        valuation k ((Y : Matrix (Fin n) (Fin n) k) p q) := le_antisymm (hle i q) (not_lt.mp hne)
    by_cases hiq : G.bl i < G.bl q
    · have := hmin (i, q) (by simp [heq, hpq])
      have h1' := Fin.lt_def.mp hi
      have h2' := Fin.lt_def.mp hiq
      simp only at this
      omega
    · have := hsmall i q hiq
      rw [heq] at this
      exact absurd this (not_le.mpr hgt)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Establish `e : ((1 + vecMulVec u w : Matrix (Fin n) (Fin n) k).submatrix (Subtype.val : {i // P i} → Fin n) Subtype.val) = (1 + vecMulVec (fun i : {i // P i} => u i) (fun i : {i // P i} => w i) : Matrix {i // P i} {i // P i} k)`. Use extensionality with `i j`. Simplify using `[Matrix.one_apply, vecMulVec_apply, Subtype.ext_iff]`. Rewrite using `[e]`. Rewrite using `[vecMulVec_eq (ι := Unit), det_one_add_replicateCol_mul_replicateRow]`.

Simplify using `[dotProduct]`.
-/
theorem det_submatrix_one_add {n : ℕ} (P : Fin n → Prop) [DecidablePred P] (u w : Fin n → k) :
    ((1 + vecMulVec u w : Matrix (Fin n) (Fin n) k).submatrix (Subtype.val : {i // P i} → Fin n)
        Subtype.val).det = 1 + ∑ i : {i // P i}, w i * u i := by
  have e : ((1 + vecMulVec u w : Matrix (Fin n) (Fin n) k).submatrix (Subtype.val : {i // P i} → Fin n)
      Subtype.val) = (1 + vecMulVec (fun i : {i // P i} => u i) (fun i : {i // P i} => w i) :
        Matrix {i // P i} {i // P i} k) := by
    ext i j
    simp [Matrix.one_apply, vecMulVec_apply, Subtype.ext_iff]
  rw [e]
  rw [vecMulVec_eq (ι := Unit), det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Rewrite using `[vecMulVec_eq (ι := Unit), det_one_add_replicateCol_mul_replicateRow]`. Rewrite using `[dotProduct_single, mul_comm]`.
-/
theorem det_left {n : ℕ} (q : Fin n) (t : k) (w : Fin n → k) :
    (1 + vecMulVec (Pi.single q t) w : Matrix (Fin n) (Fin n) k).det = 1 + t * w q := by
  rw [vecMulVec_eq (ι := Unit), det_one_add_replicateCol_mul_replicateRow]
  rw [dotProduct_single, mul_comm]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Rewrite using `[vecMulVec_eq (ι := Unit), det_one_add_replicateCol_mul_replicateRow]`. Rewrite using `[single_dotProduct, one_mul]`.
-/
theorem det_right {n : ℕ} (p : Fin n) (u : Fin n → k) :
    (1 + vecMulVec u (Pi.single p 1) : Matrix (Fin n) (Fin n) k).det = 1 + u p := by
  rw [vecMulVec_eq (ι := Unit), det_one_add_replicateCol_mul_replicateRow]
  rw [single_dotProduct, one_mul]

/- English proof (translation)
Unfold `UpperTheory.TNZ.Grp.Δ`. Use `show ((g : Matrix (Fin n) (Fin n) k).submatrix (Subtype.val : {i // G.bl i ≤ a} → Fin n) Subtype.val).det = _`. Rewrite using `[hg, det_submatrix_one_add]`. Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single ⟨q, h⟩]`.

Simplify using `[mul_comm]`. Introduce `b _ hb`. Rewrite using `[Pi.single_eq_of_ne (fun e => hb (Subtype.ext e)), mul_zero]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_eq_zero, add_zero]`.

Introduce `b _`. Rewrite using `[Pi.single_eq_of_ne (fun (e : (b : Fin n) = q) => h (e ▸ b.2)), mul_zero]`.
-/
theorem Δ_left {n : ℕ} (G : Grp k n) (g : GL (Fin n) k) (q : Fin n) (t : k) (w : Fin n → k)
    (hg : (g : Matrix (Fin n) (Fin n) k) = 1 + vecMulVec (Pi.single q t) w) (a : Fin G.s) :
    G.Δ a g = if G.bl q ≤ a then 1 + t * w q else 1 := by
  unfold UpperTheory.TNZ.Grp.Δ
  show ((g : Matrix (Fin n) (Fin n) k).submatrix (Subtype.val : {i // G.bl i ≤ a} → Fin n) Subtype.val).det = _
  rw [hg, det_submatrix_one_add]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨q, h⟩]
    · simp [mul_comm]
    · intro b _ hb
      rw [Pi.single_eq_of_ne (fun e => hb (Subtype.ext e)), mul_zero]
    · simp
  · rw [Finset.sum_eq_zero, add_zero]
    intro b _
    rw [Pi.single_eq_of_ne (fun (e : (b : Fin n) = q) => h (e ▸ b.2)), mul_zero]

/- English proof (translation)
Unfold `UpperTheory.TNZ.Grp.Δ`. Use `show ((g : Matrix (Fin n) (Fin n) k).submatrix (Subtype.val : {i // G.bl i ≤ a} → Fin n) Subtype.val).det = _`. Rewrite using `[hg, det_submatrix_one_add]`. Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single ⟨p, h⟩]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[Pi.single_eq_of_ne (fun e => hb (Subtype.ext e)), zero_mul]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_eq_zero, add_zero]`.

Introduce `b _`. Rewrite using `[Pi.single_eq_of_ne (fun (e : (b : Fin n) = p) => h (e ▸ b.2)), zero_mul]`.
-/
theorem Δ_right {n : ℕ} (G : Grp k n) (g : GL (Fin n) k) (p : Fin n) (u : Fin n → k)
    (hg : (g : Matrix (Fin n) (Fin n) k) = 1 + vecMulVec u (Pi.single p 1)) (a : Fin G.s) :
    G.Δ a g = if G.bl p ≤ a then 1 + u p else 1 := by
  unfold UpperTheory.TNZ.Grp.Δ
  show ((g : Matrix (Fin n) (Fin n) k).submatrix (Subtype.val : {i // G.bl i ≤ a} → Fin n) Subtype.val).det = _
  rw [hg, det_submatrix_one_add]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨p, h⟩]
    · simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne (fun e => hb (Subtype.ext e)), zero_mul]
    · simp
  · rw [Finset.sum_eq_zero, add_zero]
    intro b _
    rw [Pi.single_eq_of_ne (fun (e : (b : Fin n) = p) => h (e ▸ b.2)), zero_mul]

/- English proof (translation)
Unfold `UpperTheory.TNZ.Grp.lam`. Set `ν : ℕ → ℂˣ` to `fun i => if h : i < G.s then G.μ ⟨i, h⟩ U else 1`. Set `hh : ℕ → ℂˣ` to `fun i => if (b : ℕ) ≤ i then ν i else ν b`. Establish `hnext : ∀ a : Fin G.s, G.μnext a U = ν (a + 1)`. Introduce `a`.

Unfold `UpperTheory.TNZ.Grp.μnext`. Distinguish the cases in `h1 : (a : ℕ) + 1 < G.s`. Simplify using `only [dif_pos h1, ν]`. Simplify using `only [dif_neg h1, ν, MonoidHom.one_apply]`. Establish `hterm : ∀ a : Fin G.s, UpperTheory.TNZ.Grp.chk (G.μ a / G.μnext a) (G.Δ a g) = ((hh a / hh (a + 1) : ℂˣ) : ℂ)`.

Introduce `a`. Rewrite using `[h a]`. Unfold `UpperTheory.TNZ.Grp.chk`. Distinguish the cases in `hba : b ≤ a`. Establish `hba' : (b : ℕ) ≤ a` using `hba`.

Establish `hba'' : (b : ℕ) ≤ a + 1` using `by omega`. Rewrite using `[if_pos hba, dif_neg U.ne_zero, Units.mk0_val, MonoidHom.div_apply, hnext]`. Simplify using `only [hh, if_pos hba', if_pos hba'', ν, dif_pos a.2, Fin.eta]`. Establish `hba' : ¬ (b : ℕ) ≤ a` using `hba`. Rewrite using `[if_neg hba, dif_neg one_ne_zero]`.

Establish `e1 : Units.mk0 (1 : k) one_ne_zero = 1` using `Units.ext rfl`. Rewrite using `[e1, map_one]`. Simplify using `only [hh, if_neg hba']`. Distinguish the cases in `hb1 : (b : ℕ) ≤ a + 1`. Establish `e2 : (b : ℕ) = a + 1` using `by omega`.

Simplify using `[e2]`. Simplify using `only [if_neg hb1, div_self', Units.val_one]`. Rewrite using `[Finset.prod_congr rfl (fun a _ => hterm a), ← Units.coe_prod]`. Establish `e3` using `Fin.prod_univ_eq_prod_range (fun i => hh i / hh (i + 1)) G.s`. Rewrite using `[e3, Finset.prod_range_div']`.

Establish `hνb : ν b = G.μ b U`. Simplify using `only [ν, dif_pos b.2, Fin.eta]`. Establish `h0 : hh 0 = ν b`. Simplify using `only [hh]`. Use `split_ifs with h1`.

Establish `e4 : (b : ℕ) = 0` using `by omega`. Rewrite using `[e4]`. Both sides reduce to the same expression. Establish `hs : hh G.s = 1`. Simplify using `only [hh, if_pos (le_of_lt b.2), ν, dif_neg (lt_irrefl _)]`.

Rewrite using `[h0, hs, hνb, div_one]`.
-/
theorem lam_of {n : ℕ} (G : Grp k n) (g : GL (Fin n) k) (U : kˣ) (b : Fin G.s)
    (h : ∀ a, G.Δ a g = if b ≤ a then (U : k) else 1) : G.lam g = ((G.μ b U : ℂˣ) : ℂ) := by
  unfold UpperTheory.TNZ.Grp.lam
  let ν : ℕ → ℂˣ := fun i => if h : i < G.s then G.μ ⟨i, h⟩ U else 1
  let hh : ℕ → ℂˣ := fun i => if (b : ℕ) ≤ i then ν i else ν b
  have hnext : ∀ a : Fin G.s, G.μnext a U = ν (a + 1) := by
    intro a
    unfold UpperTheory.TNZ.Grp.μnext
    by_cases h1 : (a : ℕ) + 1 < G.s
    · simp only [dif_pos h1, ν]
    · simp only [dif_neg h1, ν, MonoidHom.one_apply]
  have hterm : ∀ a : Fin G.s, UpperTheory.TNZ.Grp.chk (G.μ a / G.μnext a) (G.Δ a g) =
      ((hh a / hh (a + 1) : ℂˣ) : ℂ) := by
    intro a
    rw [h a]
    unfold UpperTheory.TNZ.Grp.chk
    by_cases hba : b ≤ a
    · have hba' : (b : ℕ) ≤ a := hba
      have hba'' : (b : ℕ) ≤ a + 1 := by omega
      rw [if_pos hba, dif_neg U.ne_zero, Units.mk0_val, MonoidHom.div_apply, hnext]
      simp only [hh, if_pos hba', if_pos hba'', ν, dif_pos a.2, Fin.eta]
    · have hba' : ¬ (b : ℕ) ≤ a := hba
      rw [if_neg hba, dif_neg one_ne_zero]
      have e1 : Units.mk0 (1 : k) one_ne_zero = 1 := Units.ext rfl
      rw [e1, map_one]
      simp only [hh, if_neg hba']
      by_cases hb1 : (b : ℕ) ≤ a + 1
      · have e2 : (b : ℕ) = a + 1 := by omega
        simp [e2]
      · simp only [if_neg hb1, div_self', Units.val_one]
  rw [Finset.prod_congr rfl (fun a _ => hterm a), ← Units.coe_prod]
  have e3 := Fin.prod_univ_eq_prod_range (fun i => hh i / hh (i + 1)) G.s
  rw [e3, Finset.prod_range_div']
  have hνb : ν b = G.μ b U := by
    simp only [ν, dif_pos b.2, Fin.eta]
  have h0 : hh 0 = ν b := by
    simp only [hh]
    split_ifs with h1
    · have e4 : (b : ℕ) = 0 := by omega
      rw [e4]
    · rfl
  have hs : hh G.s = 1 := by
    simp only [hh, if_pos (le_of_lt b.2), ν, dif_neg (lt_irrefl _)]
  rw [h0, hs, hνb, div_one]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Use `set Yi := ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) with hYi`. Use `set Y := (y : Matrix (Fin n) (Fin n) k) with hY`. Establish `hy : Yi * Y = 1`. Rewrite using `[hYi, hY, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]`. Rewrite using `[Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hy]`.

Use `congr 1`. Use extensionality with `i j`. Establish `hyij : ∑ c, Yi p c * Y c j = (1 : Matrix (Fin n) (Fin n) k) p j`. Rewrite using `[← hy, Matrix.mul_apply]`. Establish `e1 : ∀ c, ∑ d, Yi i d * vecMulVec (Pi.single q t) (fun m => Yi p m) d c = Yi i q * t * Yi p c`.

Introduce `c`. Rewrite using `[Finset.sum_eq_single q]`. Simplify using `[vecMulVec_apply]`. Expand and normalize the polynomial expressions, which then agree. Introduce `d _ hd`.

Simplify using `[vecMulVec_apply, Pi.single_eq_of_ne hd]`. Simplify using the standard rewrite rules. Simplify using `only [Matrix.mul_apply, e1]`. Establish `e2 : ∑ c, Yi i q * t * Yi p c * Y c j = Yi i q * t * ∑ c, Yi p c * Y c j`. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun c _ => by ring`. Rewrite using `[e2, hyij, vecMulVec_apply, Matrix.one_apply, Pi.single_apply]`. Distinguish the cases in `hpj : p = j`. Substitute `hpj` using the available equality. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Simplify using `[hpj, Ne.symm hpj]`.
-/
theorem conj_mat {n : ℕ} (y : GL (Fin n) k) (p q : Fin n) (t : k) :
    ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *
        (1 + vecMulVec (Pi.single q t) fun i => ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p i) *
        (y : Matrix (Fin n) (Fin n) k) =
      1 + vecMulVec (fun i => t * ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i q) (Pi.single p 1) := by
  set Yi := ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) with hYi
  set Y := (y : Matrix (Fin n) (Fin n) k) with hY
  have hy : Yi * Y = 1 := by
    rw [hYi, hY, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hy]
  congr 1
  ext i j
  have hyij : ∑ c, Yi p c * Y c j = (1 : Matrix (Fin n) (Fin n) k) p j := by
    rw [← hy, Matrix.mul_apply]
  have e1 : ∀ c, ∑ d, Yi i d * vecMulVec (Pi.single q t) (fun m => Yi p m) d c = Yi i q * t * Yi p c := by
    intro c
    rw [Finset.sum_eq_single q]
    · simp [vecMulVec_apply]
      ring
    · intro d _ hd
      simp [vecMulVec_apply, Pi.single_eq_of_ne hd]
    · simp
  simp only [Matrix.mul_apply, e1]
  have e2 : ∑ c, Yi i q * t * Yi p c * Y c j = Yi i q * t * ∑ c, Yi p c * Y c j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [e2, hyij, vecMulVec_apply, Matrix.one_apply, Pi.single_apply]
  by_cases hpj : p = j
  · subst hpj
    simp
    ring
  · simp [hpj, Ne.symm hpj]

/- English proof (translation)
Unfold `UpperTheory.TNZ.InPow`. Conclude with `⟨0, Ideal.zero_mem _, map_zero _⟩`.
-/
theorem inPow_zero (c : ℕ) : InPow c (0 : k) := by
  unfold UpperTheory.TNZ.InPow
  exact ⟨0, Ideal.zero_mem _, map_zero _⟩

/- English proof (translation)
Unfold `UpperTheory.TNZ.InPow`. Establish `hx1 : valuation k x ≤ 1` using `le_of_lt hx`. Set `x' : 𝒪[k]` to `⟨x, hx1⟩`. Establish `hxm : x' ∈ IsLocalRing.maximalIdeal 𝒪[k]`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]`.

Conclude with `ne_of_lt hx`. Use `⟨z * x', ?_, rfl⟩` and prove the remaining obligations. Apply `Ideal.pow_le_pow_right (show c' ≤ c - 1 + 1 by omega)` to reduce the goal to its premises. Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_mul hz hxm`.
-/
theorem inPow_mul {c c' : ℕ} (hc : c' ≤ c) {z : 𝒪[k]} (hz : z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ (c - 1))
    {x : k} (hx : valuation k x < 1) : InPow c' ((z : k) * x) := by
  unfold UpperTheory.TNZ.InPow
  have hx1 : valuation k x ≤ 1 := le_of_lt hx
  let x' : 𝒪[k] := ⟨x, hx1⟩
  have hxm : x' ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
    exact ne_of_lt hx
  refine ⟨z * x', ?_, rfl⟩
  apply Ideal.pow_le_pow_right (show c' ≤ c - 1 + 1 by omega)
  rw [pow_succ]
  exact Ideal.mul_mem_mul hz hxm

/- English proof (translation)
Establish `hne : UpperTheory.TNZ.res (G.μ a) ≠ UpperTheory.TNZ.res (G.μ b)` using `G.dist a b hab`. Distinguish the cases in `h0 : UpperTheory.TNZ.cc G.μ a b = 0`. Take `⟨u, hu⟩` from `DFunLike.ne_iff.1 hne`. Use `⟨u, ?_, fun e => hu (Units.ext e)⟩` and prove the remaining obligations. Rewrite using `[h0]`.

Simplify using the standard rewrite rules. Establish `hlt : UpperTheory.TNZ.cc G.μ a b - 1 < UpperTheory.TNZ.cc G.μ a b` using `by omega`. Establish `hnot : UpperTheory.TNZ.cc G.μ a b - 1 ∉ {c | ∀ (u : 𝒪[k]ˣ), (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c → (UpperTheory.TNZ.res (G.μ a / G.μ b)) u = 1}`. Conclude with `Nat.notMem_of_lt_sInf hlt`. Simplify using `only [Set.mem_ofPred_eq, not_forall] at hnot`.

Take `⟨u, hu, hne1⟩` from `hnot`. Use `⟨u, hu, fun e => hne1 ?_⟩` and prove the remaining obligations. Use `show G.μ a (GlobalTheory.LocGL.unitIncl k u) / G.μ b (GlobalTheory.LocGL.unitIncl k u) = 1`. Rewrite using `[div_eq_one]`. Conclude with `Units.ext e`.
-/
theorem exists_unit {n : ℕ} (G : Grp k n) {a b : Fin G.s} (hab : a ≠ b) :
    ∃ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ (cc G.μ a b - 1) ∧
      ((G.μ a (unitIncl k u) : ℂˣ) : ℂ) ≠ ((G.μ b (unitIncl k u) : ℂˣ) : ℂ) := by
  have hne : UpperTheory.TNZ.res (G.μ a) ≠ UpperTheory.TNZ.res (G.μ b) := G.dist a b hab
  by_cases h0 : UpperTheory.TNZ.cc G.μ a b = 0
  · obtain ⟨u, hu⟩ := DFunLike.ne_iff.1 hne
    refine ⟨u, ?_, fun e => hu (Units.ext e)⟩
    rw [h0]
    simp
  · have hlt : UpperTheory.TNZ.cc G.μ a b - 1 < UpperTheory.TNZ.cc G.μ a b := by omega
    have hnot : UpperTheory.TNZ.cc G.μ a b - 1 ∉ {c | ∀ (u : 𝒪[k]ˣ),
        (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c → (UpperTheory.TNZ.res (G.μ a / G.μ b)) u = 1} := by
      exact Nat.notMem_of_lt_sInf hlt
    simp only [Set.mem_ofPred_eq, not_forall] at hnot
    obtain ⟨u, hu, hne1⟩ := hnot
    refine ⟨u, hu, fun e => hne1 ?_⟩
    show G.μ a (GlobalTheory.LocGL.unitIncl k u) / G.μ b (GlobalTheory.LocGL.unitIncl k u) = 1
    rw [div_eq_one]
    exact Units.ext e

/- English proof (translation)
Establish `hz1 : valuation k (z : k) ≤ 1` using `z.2`. Apply the tactic sequence `have hentry : ∀ i j, (g : Matrix (Fin n) (Fin n) k) i j = (if i = j then 1 else 0) + (if i = q then (z : k) * r j else 0) := by`. Introduce `i j`. Rewrite using `[hg, Matrix.add_apply, Matrix.one_apply, vecMulVec_apply, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Use `show g ∈ KO k (Fin n) ∧ ∀ i j, G.bl j < G.bl i → InPow (cc G.μ (G.bl j) (G.bl i)) ((g : Matrix (Fin n) (Fin n) k) i j)`. Use `⟨mem_KO_of g (fun i j => ?_) hdet, fun i j hij => ?_⟩` and prove the remaining obligations. Rewrite using `[hentry]`. Apply `(Valuation.map_add _ _ _).trans (max_le ?_ ?_)` to reduce the goal to its premises. Apply the tactic sequence `split_ifs <;> simp`.

Use `split_ifs`. Rewrite using `[map_mul]`. Conclude with `mul_le_one' hz1 (hr j)`. Simplify using the standard rewrite rules. Establish `hne : i ≠ j` using `fun e => by subst e; exact lt_irrefl _ hij`.

Rewrite using `[hentry, if_neg hne, zero_add]`. Use `split_ifs with hiq`. Substitute `hiq` using the available equality. Distinguish the cases in `hrj : r j = 0`. Rewrite using `[hrj, mul_zero]`.

Conclude with `inPow_zero _`. Conclude with `inPow_mul (hcc j hij hrj) hz (hrlt j hij)`. Conclude with `inPow_zero _`.
-/
theorem memJ_left {n : ℕ} (G : Grp k n) (g : GL (Fin n) k) (q : Fin n) (c : ℕ) {z : 𝒪[k]}
    (hz : z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ (c - 1)) (r : Fin n → k)
    (hr : ∀ i, valuation k (r i) ≤ 1) (hrlt : ∀ i, G.bl i < G.bl q → valuation k (r i) < 1)
    (hcc : ∀ i, G.bl i < G.bl q → r i ≠ 0 → cc G.μ (G.bl i) (G.bl q) ≤ c)
    (hg : (g : Matrix (Fin n) (Fin n) k) = 1 + vecMulVec (Pi.single q (z : k)) r)
    (hdet : valuation k (g : Matrix (Fin n) (Fin n) k).det = 1) : g ∈ G.JSet := by
  have hz1 : valuation k (z : k) ≤ 1 := z.2
  have hentry : ∀ i j, (g : Matrix (Fin n) (Fin n) k) i j =
      (if i = j then 1 else 0) + (if i = q then (z : k) * r j else 0) := by
    intro i j
    rw [hg, Matrix.add_apply, Matrix.one_apply, vecMulVec_apply, Pi.single_apply]
    split_ifs <;> simp
  show g ∈ KO k (Fin n) ∧ ∀ i j, G.bl j < G.bl i →
    InPow (cc G.μ (G.bl j) (G.bl i)) ((g : Matrix (Fin n) (Fin n) k) i j)
  refine ⟨mem_KO_of g (fun i j => ?_) hdet, fun i j hij => ?_⟩
  · rw [hentry]
    apply (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · split_ifs <;> simp
    · split_ifs
      · rw [map_mul]
        exact mul_le_one' hz1 (hr j)
      · simp
  · have hne : i ≠ j := fun e => by subst e; exact lt_irrefl _ hij
    rw [hentry, if_neg hne, zero_add]
    split_ifs with hiq
    · subst hiq
      by_cases hrj : r j = 0
      · rw [hrj, mul_zero]
        exact inPow_zero _
      · exact inPow_mul (hcc j hij hrj) hz (hrlt j hij)
    · exact inPow_zero _

/- English proof (translation)
Establish `hz1 : valuation k (z : k) ≤ 1` using `z.2`. Apply the tactic sequence `have hentry : ∀ i j, (g : Matrix (Fin n) (Fin n) k) i j = (if i = j then 1 else 0) + (if j = p then (z : k) * s i else 0) := by`. Introduce `i j`. Rewrite using `[hg, Matrix.add_apply, Matrix.one_apply, vecMulVec_apply, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Use `show g ∈ KO k (Fin n) ∧ ∀ i j, G.bl j < G.bl i → InPow (cc G.μ (G.bl j) (G.bl i)) ((g : Matrix (Fin n) (Fin n) k) i j)`. Use `⟨mem_KO_of g (fun i j => ?_) hdet, fun i j hij => ?_⟩` and prove the remaining obligations. Rewrite using `[hentry]`. Apply `(Valuation.map_add _ _ _).trans (max_le ?_ ?_)` to reduce the goal to its premises. Apply the tactic sequence `split_ifs <;> simp`.

Use `split_ifs`. Rewrite using `[map_mul]`. Conclude with `mul_le_one' hz1 (hs i)`. Simplify using the standard rewrite rules. Establish `hne : i ≠ j` using `fun e => by subst e; exact lt_irrefl _ hij`.

Rewrite using `[hentry, if_neg hne, zero_add]`. Use `split_ifs with hjp`. Substitute `hjp` using the available equality. Distinguish the cases in `hsi : s i = 0`. Rewrite using `[hsi, mul_zero]`.

Conclude with `inPow_zero _`. Conclude with `inPow_mul (hcc i hij hsi) hz (hslt i hij)`. Conclude with `inPow_zero _`.
-/
theorem memJ_right {n : ℕ} (G : Grp k n) (g : GL (Fin n) k) (p : Fin n) (c : ℕ) {z : 𝒪[k]}
    (hz : z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ (c - 1)) (s : Fin n → k)
    (hs : ∀ i, valuation k (s i) ≤ 1) (hslt : ∀ i, G.bl p < G.bl i → valuation k (s i) < 1)
    (hcc : ∀ i, G.bl p < G.bl i → s i ≠ 0 → cc G.μ (G.bl p) (G.bl i) ≤ c)
    (hg : (g : Matrix (Fin n) (Fin n) k) = 1 + vecMulVec (fun i => (z : k) * s i) (Pi.single p 1))
    (hdet : valuation k (g : Matrix (Fin n) (Fin n) k).det = 1) : g ∈ G.JSet := by
  have hz1 : valuation k (z : k) ≤ 1 := z.2
  have hentry : ∀ i j, (g : Matrix (Fin n) (Fin n) k) i j =
      (if i = j then 1 else 0) + (if j = p then (z : k) * s i else 0) := by
    intro i j
    rw [hg, Matrix.add_apply, Matrix.one_apply, vecMulVec_apply, Pi.single_apply]
    split_ifs <;> simp
  show g ∈ KO k (Fin n) ∧ ∀ i j, G.bl j < G.bl i →
    InPow (cc G.μ (G.bl j) (G.bl i)) ((g : Matrix (Fin n) (Fin n) k) i j)
  refine ⟨mem_KO_of g (fun i j => ?_) hdet, fun i j hij => ?_⟩
  · rw [hentry]
    apply (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · split_ifs <;> simp
    · split_ifs
      · rw [map_mul]
        exact mul_le_one' hz1 (hs i)
      · simp
  · have hne : i ≠ j := fun e => by subst e; exact lt_irrefl _ hij
    rw [hentry, if_neg hne, zero_add]
    split_ifs with hjp
    · subst hjp
      by_cases hsi : s i = 0
      · rw [hsi, mul_zero]
        exact inPow_zero _
      · exact inPow_mul (hcc i hij hsi) hz (hslt i hij)
    · exact inPow_zero _

end P_nonint

open P_nonint in

/- English proof (translation)
Introduce `_ _ y hy hyK`. Establish `hy' : y⁻¹ ∈ unipRad k G.e` using `Subgroup.inv_mem _ hy`. Establish `hyK' : y⁻¹ ∉ KO k (Fin n)` using `fun h => hyK (by simpa using Subgroup.inv_mem _ h)`. Take `⟨p, q, hpq, h1, h2, h3, h4⟩` from `select G hy' (exists_big G hy' hyK')`. Establish `hvpos : 0 < valuation k (((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q)` using `lt_of_le_of_lt zero_le (h3 p hpq)`.

Establish `hY0 : ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q ≠ 0` using `fun h0 => by`. Rewrite `hvpos` using `[h0, map_zero]`. Conclude with `lt_irrefl _ hvpos`. Take `⟨u, hu1, hune⟩` from `exists_unit G (ne_of_lt hpq)`. Establish `hzu : 1 + (((u : 𝒪[k]) - 1 : 𝒪[k]) : k) = ((u : 𝒪[k]) : k)`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hvu : valuation k ((u : 𝒪[k]) : k) = 1` using `(Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.1 u.isUnit`. Establish `hdetJ : (1 + vecMulVec (Pi.single q ((((u : 𝒪[k]) - 1 : 𝒪[k]) : k) / ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q)) (fun i => ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p i) : Matrix (Fin n) (Fin n) k).det = ((u : 𝒪[k]) : k)`. Rewrite using `[det_left, div_mul_cancel₀ _ hY0, hzu]`.

Establish `hdet0 : (1 + vecMulVec (Pi.single q ((((u : 𝒪[k]) - 1 : 𝒪[k]) : k) / ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q)) (fun i => ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p i) : Matrix (Fin n) (Fin n) k).det ≠ 0`. Rewrite using `[hdetJ]`. Introduce `h0`. Rewrite `hvu` using `[h0, map_zero]`. Conclude with `zero_ne_one hvu`.

Take `⟨J, hJv⟩ : ∃ J : GL (Fin n) k, (J : Matrix (Fin n) (Fin n) k) = 1 + vecMulVec (Pi.single q ((((u : 𝒪[k]) - 1 : 𝒪[k]) : k) / ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q)) (fun i => ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p i)` from `⟨((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet0)).unit, IsUnit.unit_spec _⟩`. Establish `hconj : ((y⁻¹ * J * y : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 1 + vecMulVec (fun i => (((u : 𝒪[k]) - 1 : 𝒪[k]) : k) * (((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i q / ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q)) (Pi.single p 1)`. Rewrite using `[Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, hJv, conj_mat]`. Use `congr 2`. Use function extensionality and compare the values at `i`.

Rewrite using `[div_mul_eq_mul_div, mul_div_assoc]`. Establish `hJform : (J : Matrix (Fin n) (Fin n) k) = 1 + vecMulVec (Pi.single q (((u : 𝒪[k]) - 1 : 𝒪[k]) : k)) (fun i => ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p i / ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q)`. Rewrite using `[hJv]`. Use `congr 1`. Use extensionality with `i j`.

Simplify using `only [vecMulVec_apply, Pi.single_apply]`. Use `split_ifs`. Rewrite using `[div_mul_eq_mul_div, mul_div_assoc]`. Simplify using the standard rewrite rules. Establish `hdiv_le : ∀ a : k, valuation k a ≤ valuation k (((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q) → valuation k (a / ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q) ≤ 1`.

Introduce `a ha`. Rewrite using `[map_div₀]`. Conclude with `(div_le_one₀ hvpos).2 ha`. Establish `hdiv_lt : ∀ a : k, valuation k a < valuation k (((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q) → valuation k (a / ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q) < 1`. Introduce `a ha`.

Rewrite using `[map_div₀]`. Conclude with `(div_lt_one₀ hvpos).2 ha`. Establish `hJmem : J ∈ G.JSet`. Use `memJ_left G J q (UpperTheory.TNZ.cc G.μ (G.bl p) (G.bl q)) hu1 (fun i => ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p i / ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q) (fun i => hdiv_le _ (h1 i)) (fun i hi => hdiv_lt _ (h3 i hi)) (fun i hi hri => ?_) hJform ?_` and prove the remaining obligations. Establish `hYpi : ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p i ≠ 0` using `fun h0 => hri (by simp only [h0, zero_div])`.

Establish `hpi : G.bl p ≤ G.bl i`. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Apply the tactic sequence `exact hYpi ((unip_entry G hy' p i).1 hlt)`. Conclude with `G.ball _ _ _ _ hpi hi le_rfl`.

Rewrite using `[hJv, hdetJ, hvu]`. Establish `hcmem : y⁻¹ * J * y ∈ G.JSet`. Use `memJ_right G (y⁻¹ * J * y) p (UpperTheory.TNZ.cc G.μ (G.bl p) (G.bl q)) hu1 (fun i => ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i q / ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q) (fun i => hdiv_le _ (h2 i)) (fun i hi => hdiv_lt _ (h4 i hi)) (fun i hi hsi => ?_) …` and prove the remaining obligations. Establish `hYiq : ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i q ≠ 0` using `fun h0 => hsi (by simp only [h0, zero_div])`. Establish `hiq : G.bl i ≤ G.bl q`.

Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Apply the tactic sequence `exact hYiq ((unip_entry G hy' i q).1 hlt)`. Conclude with `G.ball _ _ _ _ le_rfl hi hiq`. Rewrite using `[hconj, det_right, div_self hY0, mul_one, hzu, hvu]`.

Establish `hlamJ : G.lam J = ((G.μ (G.bl q) (unitIncl k u) : ℂˣ) : ℂ)`. Apply `lam_of G J (unitIncl k u) (G.bl q)` to reduce the goal to its premises. Introduce `a`. Rewrite using `[Δ_left G J q _ _ hJv a, div_mul_cancel₀ _ hY0, hzu]`. Both sides reduce to the same expression.

Establish `hlamc : G.lam (y⁻¹ * J * y) = ((G.μ (G.bl p) (unitIncl k u) : ℂˣ) : ℂ)`. Apply `lam_of G (y⁻¹ * J * y) (unitIncl k u) (G.bl p)` to reduce the goal to its premises. Introduce `a`. Rewrite using `[Δ_right G _ p _ hconj a, div_self hY0, mul_one, hzu]`. Both sides reduce to the same expression.

Use `⟨J, hJmem, hcmem, ?_⟩` and prove the remaining obligations. Rewrite using `[hlamc, hlamJ]`. Conclude with `hune`.
-/
theorem step_nonint {n : ℕ} (G : Grp k n) : G.NonIntegralProp := by
  intro _ _ y hy hyK
  have hy' : y⁻¹ ∈ unipRad k G.e := Subgroup.inv_mem _ hy
  have hyK' : y⁻¹ ∉ KO k (Fin n) := fun h => hyK (by simpa using Subgroup.inv_mem _ h)
  obtain ⟨p, q, hpq, h1, h2, h3, h4⟩ := select G hy' (exists_big G hy' hyK')
  have hvpos : 0 < valuation k (((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q) := lt_of_le_of_lt zero_le (h3 p hpq)
  have hY0 : ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hvpos
    exact lt_irrefl _ hvpos
  obtain ⟨u, hu1, hune⟩ := exists_unit G (ne_of_lt hpq)
  have hzu : 1 + (((u : 𝒪[k]) - 1 : 𝒪[k]) : k) = ((u : 𝒪[k]) : k) := by
    push_cast
    ring
  have hvu : valuation k ((u : 𝒪[k]) : k) = 1 :=
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.1 u.isUnit
  have hdetJ : (1 + vecMulVec (Pi.single q ((((u : 𝒪[k]) - 1 : 𝒪[k]) : k) / ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q)) (fun i => ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p i) :
      Matrix (Fin n) (Fin n) k).det = ((u : 𝒪[k]) : k) := by
    rw [det_left, div_mul_cancel₀ _ hY0, hzu]
  have hdet0 : (1 + vecMulVec (Pi.single q ((((u : 𝒪[k]) - 1 : 𝒪[k]) : k) / ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q)) (fun i => ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p i) :
      Matrix (Fin n) (Fin n) k).det ≠ 0 := by
    rw [hdetJ]
    intro h0
    rw [h0, map_zero] at hvu
    exact zero_ne_one hvu
  obtain ⟨J, hJv⟩ : ∃ J : GL (Fin n) k, (J : Matrix (Fin n) (Fin n) k) =
      1 + vecMulVec (Pi.single q ((((u : 𝒪[k]) - 1 : 𝒪[k]) : k) / ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q)) (fun i => ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p i) :=
    ⟨((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet0)).unit, IsUnit.unit_spec _⟩
  have hconj : ((y⁻¹ * J * y : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      1 + vecMulVec (fun i => (((u : 𝒪[k]) - 1 : 𝒪[k]) : k) * (((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i q / ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q)) (Pi.single p 1) := by
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, hJv, conj_mat]
    congr 2
    funext i
    rw [div_mul_eq_mul_div, mul_div_assoc]
  have hJform : (J : Matrix (Fin n) (Fin n) k) =
      1 + vecMulVec (Pi.single q (((u : 𝒪[k]) - 1 : 𝒪[k]) : k)) (fun i => ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p i / ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q) := by
    rw [hJv]
    congr 1
    ext i j
    simp only [vecMulVec_apply, Pi.single_apply]
    split_ifs
    · rw [div_mul_eq_mul_div, mul_div_assoc]
    · simp
  have hdiv_le : ∀ a : k, valuation k a ≤ valuation k (((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q) → valuation k (a / ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q) ≤ 1 := by
    intro a ha
    rw [map_div₀]
    exact (div_le_one₀ hvpos).2 ha
  have hdiv_lt : ∀ a : k, valuation k a < valuation k (((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q) → valuation k (a / ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q) < 1 := by
    intro a ha
    rw [map_div₀]
    exact (div_lt_one₀ hvpos).2 ha
  have hJmem : J ∈ G.JSet := by
    refine memJ_left G J q (UpperTheory.TNZ.cc G.μ (G.bl p) (G.bl q)) hu1 (fun i => ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p i / ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q)
      (fun i => hdiv_le _ (h1 i)) (fun i hi => hdiv_lt _ (h3 i hi)) (fun i hi hri => ?_) hJform ?_
    · have hYpi : ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p i ≠ 0 := fun h0 => hri (by simp only [h0, zero_div])
      have hpi : G.bl p ≤ G.bl i := by
        by_contra hlt
        push Not at hlt
        exact hYpi ((unip_entry G hy' p i).1 hlt)
      exact G.ball _ _ _ _ hpi hi le_rfl
    · rw [hJv, hdetJ, hvu]
  have hcmem : y⁻¹ * J * y ∈ G.JSet := by
    refine memJ_right G (y⁻¹ * J * y) p (UpperTheory.TNZ.cc G.μ (G.bl p) (G.bl q)) hu1 (fun i => ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i q / ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q)
      (fun i => hdiv_le _ (h2 i)) (fun i hi => hdiv_lt _ (h4 i hi)) (fun i hi hsi => ?_) hconj ?_
    · have hYiq : ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i q ≠ 0 := fun h0 => hsi (by simp only [h0, zero_div])
      have hiq : G.bl i ≤ G.bl q := by
        by_contra hlt
        push Not at hlt
        exact hYiq ((unip_entry G hy' i q).1 hlt)
      exact G.ball _ _ _ _ le_rfl hi hiq
    · rw [hconj, det_right, div_self hY0, mul_one, hzu, hvu]
  have hlamJ : G.lam J = ((G.μ (G.bl q) (unitIncl k u) : ℂˣ) : ℂ) := by
    apply lam_of G J (unitIncl k u) (G.bl q)
    intro a
    rw [Δ_left G J q _ _ hJv a, div_mul_cancel₀ _ hY0, hzu]
    rfl
  have hlamc : G.lam (y⁻¹ * J * y) = ((G.μ (G.bl p) (unitIncl k u) : ℂˣ) : ℂ) := by
    apply lam_of G (y⁻¹ * J * y) (unitIncl k u) (G.bl p)
    intro a
    rw [Δ_right G _ p _ hconj a, div_self hY0, mul_one, hzu]
    rfl
  refine ⟨J, hJmem, hcmem, ?_⟩
  rw [hlamc, hlamJ]
  exact hune

end UpperTheory.TNZ.Grp
