import Development.WeilBound.ThetaLifts.SmallCones.SoDefs
import Development.WeilBound.ThetaLifts.SmallCones.SoStab

noncomputable section

namespace PositivityTheory.ThKCT.So

open Filter Topology NumberField IsDedekindDomain Matrix GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.CompanionTheory.Ar.RT.Move GlobalTheory.LatVac PositivityTheory.KCo GlobalTheory.ThK
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField Classical.propDecidable

/- English proof (translation)
Use `choose! m c hm hne hN using h`. Establish `key : ∀ s : Finset X, (∀ Y ∈ s, Y ∉ Z) → ∀ Φ ∈ SB X, (∀ y, Φ y ≠ 0 → ∃ Y ∈ s, m Y y = m Y Y) → Φ ∈ N`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`.

Introduce `_ Φ _ h0`. Establish `: Φ = 0` using `funext fun y => by by_contra e; simpa using h0 y e`. Rewrite using `[this]`. Conclude with `zero_mem _`. Consider the case `insert Y s hY ih`.

Introduce `hs Φ hΦ h0`. Establish `hY1` using `hs Y (Finset.mem_insert_self _ _)`. Establish `hU : IsClopen {y | m Y y = m Y Y}` using `(hm Y hY1).isClopen_fiber _`. Establish `h1` using `hN Y hY1 _ (Submodule.smul_mem _ (m Y Y - c Y)⁻¹ (indicator_mem hU hΦ))`. Establish `h2` using `ih (fun Z hZ => hs Z (Finset.mem_insert_of_mem hZ)) _ (indicator_mem hU.compl hΦ) fun y hy => by`.

Establish `hy1 : y ∈ {y | m Y y = m Y Y}ᶜ` using `Set.mem_of_indicator_ne_zero hy`. Rewrite `hy` using `[Set.indicator_of_mem hy1]`. Take `⟨Z, hZ, e⟩` from `h0 y hy`. Break down `Finset.mem_insert.1 hZ with rfl | hZ` into its components or cases. Conclude with `(hy1 e).elim`.

Conclude with `⟨Z, hZ, e⟩`. Use `add_mem h1 h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `y`. Distinguish the cases in `hy : y ∈ {y | m Y y = m Y Y}`. Establish `e : m Y y = m Y Y` using `hy`.

Establish `: y ∉ {y | m Y y = m Y Y}ᶜ` using `fun h => h hy`. Simplify using `only [Pi.add_apply, Pi.smul_apply, Set.indicator_of_mem hy, Set.indicator_of_notMem this, e, smul_eq_mul]`. Rewrite using `[mul_inv_cancel_left₀ (sub_ne_zero.2 (hne Y hY1)), add_zero]`. Simplify using `[Set.indicator_of_notMem hy, Set.indicator_of_mem (show y ∈ {y | m Y y = m Y Y}ᶜ from hy)]`. Introduce `Φ hΦ h1`.

Establish `hK : IsCompact {y | Φ y ≠ 0}` using `hΦ.2.isCompact.of_isClosed_subset (hΦ.1.isClopen_fiber 0).compl.1 subset_closure`. Take `⟨s, hs, hc⟩` from `hK.elim_nhds_subcover (fun Y => {y | m Y y = m Y Y}) fun Y hY => ((hm Y fun e => hY (h1 Y e)).isOpen_fiber _).mem_nhds rfl`. Use `key s (fun Y hY e => hs Y hY (h1 Y e)) Φ hΦ fun y hy => ?_` and prove the remaining obligations. Simplify using `using hc hy`.
-/
theorem kill_set {X : Type} [TopologicalSpace X] (N : Submodule ℂ (X → ℂ)) (Z : Set X)
    (h : ∀ Y ∉ Z, ∃ (m : X → ℂ) (c : ℂ), IsLocallyConstant m ∧ m Y ≠ c ∧ ∀ Φ ∈ SB X, (fun y => (m y - c) * Φ y) ∈ N) :
    ∀ Φ ∈ SB X, (∀ Y ∈ Z, Φ Y = 0) → Φ ∈ N := by
  classical
  choose! m c hm hne hN using h
  have key : ∀ s : Finset X, (∀ Y ∈ s, Y ∉ Z) → ∀ Φ ∈ SB X, (∀ y, Φ y ≠ 0 → ∃ Y ∈ s, m Y y = m Y Y) → Φ ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _ Φ _ h0
      have : Φ = 0 := funext fun y => by by_contra e; simpa using h0 y e
      rw [this]; exact zero_mem _
    | insert Y s hY ih =>
      intro hs Φ hΦ h0
      have hY1 := hs Y (Finset.mem_insert_self _ _)
      have hU : IsClopen {y | m Y y = m Y Y} := (hm Y hY1).isClopen_fiber _
      have h1 := hN Y hY1 _ (Submodule.smul_mem _ (m Y Y - c Y)⁻¹ (indicator_mem hU hΦ))
      have h2 := ih (fun Z hZ => hs Z (Finset.mem_insert_of_mem hZ)) _ (indicator_mem hU.compl hΦ) fun y hy => by
        have hy1 : y ∈ {y | m Y y = m Y Y}ᶜ := Set.mem_of_indicator_ne_zero hy
        rw [Set.indicator_of_mem hy1] at hy
        obtain ⟨Z, hZ, e⟩ := h0 y hy
        rcases Finset.mem_insert.1 hZ with rfl | hZ
        · exact (hy1 e).elim
        · exact ⟨Z, hZ, e⟩
      convert add_mem h1 h2 using 1
      funext y
      by_cases hy : y ∈ {y | m Y y = m Y Y}
      · have e : m Y y = m Y Y := hy
        have : y ∉ {y | m Y y = m Y Y}ᶜ := fun h => h hy
        simp only [Pi.add_apply, Pi.smul_apply, Set.indicator_of_mem hy, Set.indicator_of_notMem this, e, smul_eq_mul]
        rw [mul_inv_cancel_left₀ (sub_ne_zero.2 (hne Y hY1)), add_zero]
      · simp [Set.indicator_of_notMem hy, Set.indicator_of_mem (show y ∈ {y | m Y y = m Y Y}ᶜ from hy)]
  intro Φ hΦ h1
  have hK : IsCompact {y | Φ y ≠ 0} :=
    hΦ.2.isCompact.of_isClosed_subset (hΦ.1.isClopen_fiber 0).compl.1 subset_closure
  obtain ⟨s, hs, hc⟩ := hK.elim_nhds_subcover (fun Y => {y | m Y y = m Y Y}) fun Y hY =>
    ((hm Y fun e => hY (h1 Y e)).isOpen_fiber _).mem_nhds rfl
  refine key s (fun Y hY e => hs Y hY (h1 Y e)) Φ hΦ fun y hy => ?_
  simpa using hc hy

/- English proof (translation)
Establish `h` using `LinearMap.finrank_range_add_finrank_ker Cᵀ.mulVecLin`. Rewrite `h` using `[Module.finrank_fin_fun, ← Matrix.rank, Matrix.rank_transpose]`. Establish `: C.rank ≠ n ↔ LinearMap.ker Cᵀ.mulVecLin ≠ ⊥`. Rewrite using `[Ne, Ne, ← Submodule.finrank_eq_zero]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[this, Submodule.ne_bot_iff]`. Use `exists_congr fun p => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose, and_comm]`.
-/
theorem rank_ne_iff {k : Type} [Field k] {n d : ℕ} (C : Matrix (Fin n) (Fin d) k) : C.rank ≠ n ↔ ∃ p, p ≠ 0 ∧ p ᵥ* C = 0 := by
  have h := LinearMap.finrank_range_add_finrank_ker Cᵀ.mulVecLin
  rw [Module.finrank_fin_fun, ← Matrix.rank, Matrix.rank_transpose] at h
  have : C.rank ≠ n ↔ LinearMap.ker Cᵀ.mulVecLin ≠ ⊥ := by
    rw [Ne, Ne, ← Submodule.finrank_eq_zero]
    omega
  rw [this, Submodule.ne_bot_iff]
  refine exists_congr fun p => ?_
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose, and_comm]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {ψ : AddChar (AF F) ℂ}

/- English proof (translation)
Use `choose xo a1 a2 a3 using exists_coB h t hX hW`. Establish `hb` using `hι.bij`. Establish `key` using `kill_set ((SB _ ⊓ LinearMap.ker l).map ι) {Y | ∀ a ∈ A, ψ (sy σ X W (xo Y) a.1) = a.2} (fun Y hY => ?_) _ (hb.1 hφ) fun Y hY => by rw [← a3 Y]; exact hz _ (a1 Y) (a2 Y) hY`. Take `⟨φ', h', e⟩` from `key`. Rewrite using `[← hb.2.1 h'.1 hφ e]`.

Conclude with `h'.2`. Simplify using `only [Set.mem_setOf_eq, not_forall] at hY`. Take `⟨⟨u, c⟩, ha, hne⟩` from `hY`. Take `⟨hu, h1⟩` from `hA _ ha`. Set `m : Matrix (Fin n) (Fin d) (Fv F v) → ℂ` to `fun y => ψ (sy σ X W (xo y) u)`.

Establish `hm : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ι (locRho M ψ v u φ) = fun y => m y * ι φ y` using `fun φ hφ => funext fun y => by`. Use `mult' M hψ hι hu h1 (a1 y) (a2 y) hφ` as an intermediate fact. Rewrite `this` using `[a3]`. Then use the resulting hypothesis. Use `haveI : T2Space (Matrix (Fin n) (Fin d) (Fv F v)) := inferInstanceAs (T2Space (Fin n → Fin d → Fv F v))`. Use `haveI : LocallyCompactSpace (Matrix (Fin n) (Fin d) (Fv F v)) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin d → Fv F v))`.

Use `haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin d) (Fv F v)) := inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin d → Fv F v))`. Use `⟨m, c, lc_of_mul m fun Φ hΦ => ?_, hne, fun Φ hΦ => ?_⟩` and prove the remaining obligations. Take `⟨φ', h', rfl⟩` from `hb.2.2 hΦ`. Rewrite using `[← hm φ' h']`. Conclude with `hb.1 (locRho_mem M hψ u h')`.

Take `⟨φ', h', rfl⟩` from `hb.2.2 hΦ`. Use `⟨locRho M ψ v u φ' - c • φ', ⟨sub_mem (locRho_mem M hψ u h') (Submodule.smul_mem _ _ h'), ?_⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `l _ = 0`. Rewrite using `[map_sub, map_smul, hl _ ha φ' h', smul_eq_mul, sub_self]`. Rewrite using `[map_sub, map_smul, hm φ' h']`.

Use function extensionality and compare the values at `y`. Simplify using `[sub_mul]`.
-/
theorem eigen_kill_set (h : IsCMExt F E σ) (hψ : IsStd ψ) (hX : X.J.det ≠ 0) (hW : W.J.det ≠ 0) {t : E →ₐ[F] Fv F v} {ι}
    (hι : M.IsLinBar ψ t 1 1 ι) (l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ)
    (A : Set (Matrix (Fin n) (Fin d) (AE F E) × ℂ)) (hA : ∀ a ∈ A, At (evFin F v) a.1 ∧ a.1.map (piW (t.comp σ)) = 0)
    (hl : ∀ a ∈ A, ∀ φ ∈ SB _, l (locRho M ψ v a.1 φ) = a.2 * l φ) {φ} (hφ : φ ∈ SB (Fin n × Fin d → Fv F v))
    (hz : ∀ x, At (evFin F v) x → x.map (piW t) = 0 → (∀ a ∈ A, ψ (sy σ X W x a.1) = a.2) → ι φ (coB σ X W t x) = 0) :
    l φ = 0 := by
  choose xo a1 a2 a3 using exists_coB h t hX hW
  have hb := hι.bij
  have key := kill_set ((SB _ ⊓ LinearMap.ker l).map ι) {Y | ∀ a ∈ A, ψ (sy σ X W (xo Y) a.1) = a.2} (fun Y hY => ?_) _ (hb.1 hφ)
    fun Y hY => by rw [← a3 Y]; exact hz _ (a1 Y) (a2 Y) hY
  · obtain ⟨φ', h', e⟩ := key
    rw [← hb.2.1 h'.1 hφ e]
    exact h'.2
  simp only [Set.mem_setOf_eq, not_forall] at hY
  obtain ⟨⟨u, c⟩, ha, hne⟩ := hY
  obtain ⟨hu, h1⟩ := hA _ ha
  let m : Matrix (Fin n) (Fin d) (Fv F v) → ℂ := fun y => ψ (sy σ X W (xo y) u)
  have hm : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ι (locRho M ψ v u φ) = fun y => m y * ι φ y := fun φ hφ => funext fun y => by
    have := mult' M hψ hι hu h1 (a1 y) (a2 y) hφ
    rwa [a3] at this
  haveI : T2Space (Matrix (Fin n) (Fin d) (Fv F v)) := inferInstanceAs (T2Space (Fin n → Fin d → Fv F v))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin d) (Fv F v)) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin d → Fv F v))
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin d) (Fv F v)) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin d → Fv F v))
  refine ⟨m, c, lc_of_mul m fun Φ hΦ => ?_, hne, fun Φ hΦ => ?_⟩
  · obtain ⟨φ', h', rfl⟩ := hb.2.2 hΦ
    rw [← hm φ' h']
    exact hb.1 (locRho_mem M hψ u h')
  · obtain ⟨φ', h', rfl⟩ := hb.2.2 hΦ
    refine ⟨locRho M ψ v u φ' - c • φ', ⟨sub_mem (locRho_mem M hψ u h') (Submodule.smul_mem _ _ h'), ?_⟩, ?_⟩
    · change l _ = 0
      rw [map_sub, map_smul, hl _ ha φ' h', smul_eq_mul, sub_self]
    · rw [map_sub, map_smul, hm φ' h']
      funext y
      simp [sub_mul]

include M in
/- English proof (translation)
Simplify using `only [sy, M.co.form, map_smul, Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_dotProduct, smul_eq_mul, mul_sub]`.
-/
theorem sy_smul (x u : Matrix (Fin n) (Fin d) (AE F E)) (a : AF F) : sy σ X W x (a • u) = a * sy σ X W x u := by
  simp only [sy, M.co.form, map_smul, Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_dotProduct, smul_eq_mul, mul_sub]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[incM, vecMulVec_apply, ht]`.
-/
theorem map_vec (π : AE F E →+* Fv F v) (t : E → Fv F v) (ht : ∀ x, π (inclR (F := F) (AF F) x) = t x) (ε : AE F E) (p : Fin n → E)
    (q : Fin d → E) : (ε • incM F (vecMulVec p q)).map π = π ε • vecMulVec (fun i => t (p i)) fun j => t (q j) := by
  ext i j
  simp [incM, vecMulVec_apply, ht]

/- English proof (translation)
Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem trace_vec {k : Type} [Field k] (C : Matrix (Fin n) (Fin d) k) (p : Fin n → k) (q : Fin d → k) :
    (Cᵀ * vecMulVec p q).trace = p ⬝ᵥ C *ᵥ q := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Use `show splitProj t (compFin F E v ((1 : AF F) ⊗ₜ[F] x)) = t x`. Establish `: compFin F E v ((1 : AF F) ⊗ₜ[F] x) = 1 ⊗ₜ[F] x` using `congrArg (· ⊗ₜ[F] x) (map_one (evFin F v))`. Rewrite using `[this, splitProj_tmul, one_mul]`.
-/
theorem piW_inc (t : E →ₐ[F] Fv F v) (x : E) : piW t (inclR (F := F) (AF F) x) = t x := by
  show splitProj t (compFin F E v ((1 : AF F) ⊗ₜ[F] x)) = t x
  have : compFin F E v ((1 : AF F) ⊗ₜ[F] x) = 1 ⊗ₜ[F] x :=
    congrArg (· ⊗ₜ[F] x) (map_one (evFin F v))
  rw [this, splitProj_tmul, one_mul]

/- English proof (translation)
Introduce `a ha` and use `by rw [smul_smul, ← smul_eq_mul, at_liftV v c a ha, zero_smul]`.
-/
theorem at_lift (c : Fv F v) (u : Matrix (Fin n) (Fin d) (AE F E)) : At (evFin F v) (liftV v c • u) := fun a ha => by
  rw [smul_smul, ← smul_eq_mul, at_liftV v c a ha, zero_smul]

/- English proof (translation)
Use `(Submodule.span_le.2 ?_ : M.So ψ t ≤ _) h` and prove the remaining obligations. Introduce and unpack `_ ⟨f, φ, h1, h2, -, rfl⟩`. Take `⟨g, hg, e⟩` from `GlobalTheory.CompanionTheory.Ar.RT.Inj.pure_eq_pureA M ψ hM φ h1 h2`. Rewrite using `[e f]`. Conclude with `Submodule.subset_span ⟨f, g, hg, rfl⟩`.
-/
theorem so_le (hM : M.IsGood ψ) (t : E →ₐ[F] Fv F v) {Ψ} (h : Ψ ∈ M.So ψ t) : Ψ ∈ schA F (Fin n × Fin d) := by
  refine (Submodule.span_le.2 ?_ : M.So ψ t ≤ _) h
  rintro _ ⟨f, φ, h1, h2, -, rfl⟩
  obtain ⟨g, hg, e⟩ := GlobalTheory.CompanionTheory.Ar.RT.Inj.pure_eq_pureA M ψ hM φ h1 h2
  rw [e f]
  exact Submodule.subset_span ⟨f, g, hg, rfl⟩

/- English proof (translation)
Use `fun Φ hΦ => (Submodule.span_le (p := LinearMap.ker L)).2 ?_ hΦ` and prove the remaining obligations. Introduce and unpack `_ ⟨f, φ, h1, h2, ⟨hv, ι, hι, h3⟩, rfl⟩`. Take `⟨r, hr, er⟩` from `GlobalTheory.CompanionTheory.Ar.RT.Inj.pure_at M B.ψ hM φ h2 f v`. Establish `hsch : ∀ φ' ∈ SB (Fin n × Fin d → Fv F v), tens (evFin F v) φ' r ∈ schA F (Fin n × Fin d)` using `fun φ' h' => by`. Establish `e` using `er (Function.update φ v φ') fun w hw => Function.update_of_ne hw _ _`.

Rewrite `e` using `[Function.update_self]`. Take `⟨g, hg, e'⟩` from `GlobalTheory.CompanionTheory.Ar.RT.Inj.pure_eq_pureA M B.ψ hM (Function.update φ v φ') (fun w => by`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Simplify using `using h'`.

Rewrite using `[Function.update_of_ne hw]`. Conclude with `h1 w) (by`. Use `filter_upwards [h2, Filter.eventually_cofinite_ne v] with w h h'`. Rewrite using `[Function.update_of_ne h', h])`. Rewrite using `[← e, e' f]`.

Conclude with `Submodule.subset_span ⟨f, g, hg, rfl⟩`. Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker, er φ fun _ _ => rfl]`. Set `l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ` to `{ toFun := fun φ' => L (tens (evFin F v) φ' r) map_add' := fun a b => by`. Establish `e : tens (evFin F v) (a + b) r = tens (evFin F v) a r + tens (evFin F v) b r` using `funext fun _ => add_mul _ _ _`. Rewrite using `[e, map_add]`.

Use the proof step `map_smul' := fun c a => by`. Establish `e : tens (evFin F v) (c • a) r = c • tens (evFin F v) a r` using `funext fun _ => mul_assoc _ _ _`. Rewrite using `[e, map_smul]`. Use `rfl }`. Take `⟨ε, e0, e1, e2⟩` from `exists_pair hB.cm t 1 0`.

Establish `hat : ∀ (c : Fv F v) (u : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) (liftV v c • u)` using `at_lift`. Use `eigen_kill_set M hB.cm hB.std (det_herm hX) (det_skew hW) hι l {b | ∃ a ∈ S, ∃ c : Fv F v, b = (liftV v c • ε • incM F (vecMulVec a.1 a.2.1), B.ψ (liftV v (a.2.2 * c)))} ?_ ?_ hv fun x hx h0 hc => h3 _ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, -, c, rfl⟩`. Use `⟨hat _ _, ?_⟩` and prove the remaining obligations. Rewrite using `[← smul_assoc, map_vec _ _ (piW_inc _), Algebra.smul_def, map_mul, e2, mul_zero, zero_smul]`.

Introduce and unpack `_ ⟨a, ha, c, rfl⟩ φ' h'`. Express the relevant statement in the definitionally equal form `L (tens _ (locRho M B.ψ v _ φ') r) = _ * L _`. Rewrite using `[← rho_tens M B.ψ (hat _ _) φ' hr, hS a ha ε e0 e1 e2 c _ (hsch φ' h')]`. Choose the witnesses or unpack the hypotheses as in `⟨s₀, hs₀⟩ : ∃ s₀, B.ψ (liftV v s₀) ≠ 1 := by`. Assume the negation of the conclusion as `e`.

Use `push Not at e`. Conclude with `GlobalTheory.PsiNontriv.psiV_ne_one B.ψ hB.std v (AddChar.ext _ _ e)`. Take `⟨p, hp, e⟩` from `hz (X.J.map t * x.map (piW (t.comp σ)) * (W.J.map t)ᵀ) fun a ha => by`. Establish `k1` using `(hL F E σ B n d X W M _ _ _ _ hB hX hW v t).2 x (ε • incM F (vecMulVec a.1 a.2.1)) hx h0`. Rewrite `k1` using `[map_vec _ _ (piW_inc _), e1, one_smul, trace_vec]`.

Rewrite using `[← k1]`. Assume the negation of the conclusion as `hne`. Use `set b := evFin F v (sy σ X W x (ε • incM F (vecMulVec a.1 a.2.1)))`. Establish `k2` using `hc _ ⟨a, ha, s₀ / (b - a.2.2), rfl⟩`. Simplify using `only at k2`.

Rewrite `k2` using `[sy_smul M, mul_comm, mul_liftV]`. Establish `k3 : b * (s₀ / (b - a.2.2)) = s₀ + a.2.2 * (s₀ / (b - a.2.2))`. Use `sub_ne_zero.2 hne` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite `k2` using `[k3, map_add, AddChar.map_add_eq_mul]`. Use `hs₀ ((mul_eq_right₀ fun e0 => ?_).1 k2)` and prove the remaining obligations. Use `GlobalTheory.StdCharFromIsStd.norm_psi hB.std (liftV v (a.2.2 * (s₀ / (b - a.2.2))))` as an intermediate fact. Rewrite `this` using `[e0, norm_zero]`. Conclude with `zero_ne_one this`.

Use `(rank_ne_iff _).2 ⟨p, hp, ?_⟩` and prove the remaining obligations. Rewrite using `[coB_eq, Matrix.neg_mul, Matrix.neg_mul, Matrix.vecMul_neg, e, neg_zero]`.
-/
theorem so_kill (hL : LinEx) {B : Base F E} {r s r' s' : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    (hM : M.IsGood B.ψ) (t : E →ₐ[F] Fv F v) (L : Fn F n d →ₗ[ℂ] ℂ) (S : Set ((Fin n → E) × (Fin d → E) × Fv F v))
    (hS : ∀ a ∈ S, ∀ ε : AE F E, At (evFin F v) ε → piW t ε = 1 → piW (t.comp σ) ε = 0 → ∀ c : Fv F v, ∀ Φ ∈ schA F _,
      L (M.co.rho B.ψ (liftV v c • ε • incM F (vecMulVec a.1 a.2.1)) Φ) = B.ψ (liftV v (a.2.2 * c)) * L Φ)
    (hz : ∀ C : Matrix (Fin n) (Fin d) (Fv F v), (∀ a ∈ S, (fun i => t (a.1 i)) ⬝ᵥ C *ᵥ (fun j => t (a.2.1 j)) = a.2.2) →
      ∃ p, p ≠ 0 ∧ p ᵥ* C = 0) : ∀ Φ ∈ M.So B.ψ t, L Φ = 0 := by
  refine fun Φ hΦ => (Submodule.span_le (p := LinearMap.ker L)).2 ?_ hΦ
  rintro _ ⟨f, φ, h1, h2, ⟨hv, ι, hι, h3⟩, rfl⟩
  obtain ⟨r, hr, er⟩ := GlobalTheory.CompanionTheory.Ar.RT.Inj.pure_at M B.ψ hM φ h2 f v
  have hsch : ∀ φ' ∈ SB (Fin n × Fin d → Fv F v), tens (evFin F v) φ' r ∈ schA F (Fin n × Fin d) := fun φ' h' => by
    have e := er (Function.update φ v φ') fun w hw => Function.update_of_ne hw _ _
    rw [Function.update_self] at e
    obtain ⟨g, hg, e'⟩ := GlobalTheory.CompanionTheory.Ar.RT.Inj.pure_eq_pureA M B.ψ hM (Function.update φ v φ') (fun w => by
      by_cases hw : w = v
      · subst hw
        simpa using h'
      · rw [Function.update_of_ne hw]
        exact h1 w) (by
      filter_upwards [h2, Filter.eventually_cofinite_ne v] with w h h'
      rw [Function.update_of_ne h', h])
    rw [← e, e' f]
    exact Submodule.subset_span ⟨f, g, hg, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, er φ fun _ _ => rfl]
  let l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun φ' => L (tens (evFin F v) φ' r)
      map_add' := fun a b => by
        have e : tens (evFin F v) (a + b) r = tens (evFin F v) a r + tens (evFin F v) b r := funext fun _ => add_mul _ _ _
        rw [e, map_add]
      map_smul' := fun c a => by
        have e : tens (evFin F v) (c • a) r = c • tens (evFin F v) a r := funext fun _ => mul_assoc _ _ _
        rw [e, map_smul]
        rfl }
  obtain ⟨ε, e0, e1, e2⟩ := exists_pair hB.cm t 1 0
  have hat : ∀ (c : Fv F v) (u : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) (liftV v c • u) := at_lift
  refine eigen_kill_set M hB.cm hB.std (det_herm hX) (det_skew hW) hι l
    {b | ∃ a ∈ S, ∃ c : Fv F v, b = (liftV v c • ε • incM F (vecMulVec a.1 a.2.1), B.ψ (liftV v (a.2.2 * c)))} ?_ ?_ hv
    fun x hx h0 hc => h3 _ ?_
  · rintro _ ⟨a, -, c, rfl⟩
    refine ⟨hat _ _, ?_⟩
    rw [← smul_assoc, map_vec _ _ (piW_inc _), Algebra.smul_def, map_mul, e2, mul_zero, zero_smul]
  · rintro _ ⟨a, ha, c, rfl⟩ φ' h'
    change L (tens _ (locRho M B.ψ v _ φ') r) = _ * L _
    rw [← rho_tens M B.ψ (hat _ _) φ' hr, hS a ha ε e0 e1 e2 c _ (hsch φ' h')]
  obtain ⟨s₀, hs₀⟩ : ∃ s₀, B.ψ (liftV v s₀) ≠ 1 := by
    by_contra e
    push Not at e
    exact GlobalTheory.PsiNontriv.psiV_ne_one B.ψ hB.std v (AddChar.ext _ _ e)
  obtain ⟨p, hp, e⟩ := hz (X.J.map t * x.map (piW (t.comp σ)) * (W.J.map t)ᵀ) fun a ha => by
    have k1 := (hL F E σ B n d X W M _ _ _ _ hB hX hW v t).2 x (ε • incM F (vecMulVec a.1 a.2.1)) hx h0
    rw [map_vec _ _ (piW_inc _), e1, one_smul, trace_vec] at k1
    rw [← k1]
    by_contra hne
    set b := evFin F v (sy σ X W x (ε • incM F (vecMulVec a.1 a.2.1)))
    have k2 := hc _ ⟨a, ha, s₀ / (b - a.2.2), rfl⟩
    simp only at k2
    rw [sy_smul M, mul_comm, mul_liftV] at k2
    have k3 : b * (s₀ / (b - a.2.2)) = s₀ + a.2.2 * (s₀ / (b - a.2.2)) := by
      have := sub_ne_zero.2 hne
      field_simp
      ring
    rw [k3, map_add, AddChar.map_add_eq_mul] at k2
    refine hs₀ ((mul_eq_right₀ fun e0 => ?_).1 k2)
    have := GlobalTheory.StdCharFromIsStd.norm_psi hB.std (liftV v (a.2.2 * (s₀ / (b - a.2.2))))
    rw [e0, norm_zero] at this
    exact zero_ne_one this
  refine (rank_ne_iff _).2 ⟨p, hp, ?_⟩
  rw [coB_eq, Matrix.neg_mul, Matrix.neg_mul, Matrix.vecMul_neg, e, neg_zero]

end PositivityTheory.ThKCT.So

end
