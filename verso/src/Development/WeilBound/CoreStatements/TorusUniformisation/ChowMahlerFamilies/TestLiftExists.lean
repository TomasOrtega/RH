import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FromNAdd
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.CharacterDataBaseChange
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.TestLift

open PositivityTheory.Xgn.A_graph_restrict_bc GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt

/- English proof (translation)
Use function extensionality and compare the values at `j`. Establish `h` using `RingHom.map_mulVec (algebraMap Ω C) (LinearMap.toMatrix' f) x j`. Rewrite `h` using `[LinearMap.toMatrix'_mulVec]`. Rewrite using `[bcLin, Matrix.toLin'_apply]`. Conclude with `h.symm`.
-/
theorem bcLin_bcMap {Ω : Type} [Field Ω] (C : Type) [Field C] [Algebra Ω C] {m n : ℕ}
    (f : (Fin m → Ω) →ₗ[Ω] (Fin n → Ω)) (x : Fin m → Ω) :
    bcLin C f (bcMap Ω C _ x) = bcMap Ω C _ (f x) := by
  funext j
  have h := RingHom.map_mulVec (algebraMap Ω C) (LinearMap.toMatrix' f) x j
  rw [LinearMap.toMatrix'_mulVec] at h
  rw [bcLin, Matrix.toLin'_apply]
  exact h.symm

/- English proof (translation)
Establish `hw' : algebraMap Ω C w ≠ 0` using `by simpa using hw`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Prove the components needed by the constructor for the conclusion. Use `map_mem (algebraMap Ω C w • LinearMap.fst C (Fin m → C) (Fin k → C)) (S' := bcMap Ω C _ '' L₁) ?_ h` as an intermediate fact.

Simplify using `using this`. Introduce and unpack `_ ⟨⟨x, z⟩, hz, rfl⟩`. Conclude with `mem_span ⟨w • x, ((hG _).1 hz).1, by simp⟩`. Use `map_mem (LinearMap.snd C (Fin m → C) (Fin k → C) - bcLin C f ∘ₗ LinearMap.fst C (Fin m → C) (Fin k → C)) (S' := bcMap Ω C _ '' L₂) ?_ h` as an intermediate fact. Simplify using `using this`.

Introduce and unpack `_ ⟨⟨x, z⟩, hz, rfl⟩`. Conclude with `mem_span ⟨z - f x, ((hG _).1 hz).2, by simp [bcLin_bcMap]⟩`. Introduce and unpack `⟨h₁, h₂⟩`. Establish `e₁` using `map_mem ((algebraMap Ω C w)⁻¹ • LinearMap.prod LinearMap.id (bcLin C f)) (S' := Prod.map (bcMap Ω C _) (bcMap Ω C _) '' G) ?_ h₁`. Establish `e₂` using `map_mem (LinearMap.inr C (Fin m → C) (Fin k → C)) (S' := Prod.map (bcMap Ω C _) (bcMap Ω C _) '' G) ?_ h₂`.

Use `AddSubgroup.add_mem _ e₁ e₂` as an intermediate fact. Rewrite `this` using `[LinearMap.smul_apply, map_smul, inv_smul_smul₀ hw']`. Simplify using `using this`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `mem_span ⟨(0, x), (hG _).2 ⟨by simp, by simpa using hx⟩, by simp⟩`.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `mem_span ⟨(w⁻¹ • x, w⁻¹ • f x), (hG _).2 ⟨by simpa [smul_inv_smul₀ hw] using hx, by simp⟩, ?_⟩` and prove the remaining obligations. Simplify using `[bcLin_bcMap, ← map_inv₀]`.
-/
theorem graph_bc {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o C] [Algebra Ω C]
    (RC : Subalgebra o C) {m k : ℕ} {w : Ω} (hw : w ≠ 0) (L₁ : AddSubgroup (Fin m → Ω))
    (L₂ : AddSubgroup (Fin k → Ω)) (f : (Fin m → Ω) →ₗ[Ω] (Fin k → Ω))
    (G : AddSubgroup ((Fin m → Ω) × (Fin k → Ω)))
    (hG : ∀ z, z ∈ G ↔ w • z.1 ∈ L₁ ∧ z.2 - f z.1 ∈ L₂) (a : Fin m → C) (b : Fin k → C) :
    (a, b) ∈ spanOver RC (Prod.map (bcMap Ω C _) (bcMap Ω C _) '' G) ↔
      algebraMap Ω C w • a ∈ spanOver RC (bcMap Ω C _ '' L₁) ∧
        b - bcLin C f a ∈ spanOver RC (bcMap Ω C _ '' L₂) := by
  have hw' : algebraMap Ω C w ≠ 0 := by simpa using hw
  constructor
  · intro h
    constructor
    · have := map_mem (algebraMap Ω C w • LinearMap.fst C (Fin m → C) (Fin k → C))
        (S' := bcMap Ω C _ '' L₁) ?_ h
      · simpa using this
      rintro _ ⟨⟨x, z⟩, hz, rfl⟩
      exact mem_span ⟨w • x, ((hG _).1 hz).1, by simp⟩
    · have := map_mem (LinearMap.snd C (Fin m → C) (Fin k → C) -
        bcLin C f ∘ₗ LinearMap.fst C (Fin m → C) (Fin k → C)) (S' := bcMap Ω C _ '' L₂) ?_ h
      · simpa using this
      rintro _ ⟨⟨x, z⟩, hz, rfl⟩
      exact mem_span ⟨z - f x, ((hG _).1 hz).2, by simp [bcLin_bcMap]⟩
  · rintro ⟨h₁, h₂⟩
    have e₁ := map_mem ((algebraMap Ω C w)⁻¹ • LinearMap.prod LinearMap.id (bcLin C f))
      (S' := Prod.map (bcMap Ω C _) (bcMap Ω C _) '' G) ?_ h₁
    · have e₂ := map_mem (LinearMap.inr C (Fin m → C) (Fin k → C))
        (S' := Prod.map (bcMap Ω C _) (bcMap Ω C _) '' G) ?_ h₂
      · have := AddSubgroup.add_mem _ e₁ e₂
        rw [LinearMap.smul_apply, map_smul, inv_smul_smul₀ hw'] at this
        simpa using this
      rintro _ ⟨x, hx, rfl⟩
      exact mem_span ⟨(0, x), (hG _).2 ⟨by simp, by simpa using hx⟩, by simp⟩
    rintro _ ⟨x, hx, rfl⟩
    refine mem_span ⟨(w⁻¹ • x, w⁻¹ • f x), (hG _).2 ⟨by simpa [smul_inv_smul₀ hw] using hx, by simp⟩, ?_⟩
    simp [bcLin_bcMap, ← map_inv₀]

section Val

variable {o C : Type} [CommRing o] [Field C] [Algebra o C] {RC : Subalgebra o C}
  {v : Valuation C NNReal}

/- English proof (translation)
Simplify using `[stdLat, AddSubgroup.mem_pi]`.
-/
theorem mem_std {κ : Type} (x : κ → C) : x ∈ stdLat RC κ ↔ ∀ i, x i ∈ RC := by
  simp [stdLat, AddSubgroup.mem_pi]

/- English proof (translation)
The claim follows from `(mem_std _).2 fun i => RC.mul_mem hc ((mem_std _).1 hx i)`.
-/
theorem std_smul {κ : Type} {c : C} (hc : c ∈ RC) {x : κ → C} (hx : x ∈ stdLat RC κ) :
    c • x ∈ stdLat RC κ :=
  (mem_std _).2 fun i => RC.mul_mem hc ((mem_std _).1 hx i)

/- English proof (translation)
Take `⟨hst, k, f, c, hf, hc, hsum, hb⟩` from `h`. Choose the witnesses or unpack the hypotheses as in `⟨l, hl⟩ : ∃ l, v (f l) = 1 := by`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `: v (∑ l, c l * f l) < 1`.

Use `v.map_sum_lt one_ne_zero fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_right ((hv _).1 (hc l)) zero_le (lt_of_le_of_ne ((hv _).1 (hf l)) (hne l))`. Rewrite `this` using `[hsum, map_one]`. Conclude with `lt_irrefl _ this`.

Establish `hf0 : f l ≠ 0`. Introduce `h0`. Rewrite `hl` using `[h0, map_zero]`. Conclude with `zero_ne_one hl`. Take `⟨b, hli, hsp, hb⟩` from `hb l`.

Use `⟨Module.Basis.mk hli hsp.ge, fun x => ?_⟩` and prove the remaining obligations. Establish `h₁ : (∃ n : ℕ, f l ^ n • x ∈ L) ↔ x ∈ L`. Use `⟨fun ⟨n, hn⟩ => ?_, fun hx => ⟨0, by simpa using hx⟩⟩` and prove the remaining obligations. Use `hst (f l ^ n)⁻¹ ((hv _).2 (by simp [hl])) _ hn` as an intermediate fact. Rewrite `this` using `[inv_smul_smul₀ (pow_ne_zero _ hf0)]`. Then use the resulting hypothesis.

Establish `h₂ : ∀ t : C, (∃ n : ℕ, f l ^ n * t ∈ RC) ↔ t ∈ RC` using `fun t => by`. Simplify using `[hv, hl]`. Rewrite using `[← h₁, hb]`. Simplify using `only [h₂]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a, ha, rfl⟩ q`. Use `(Module.Basis.mk hli hsp.ge).repr_sum_self a` as an intermediate fact. Simplify using `only [Module.Basis.coe_mk] at this`. Rewrite using `[this]`. Conclude with `ha q`.

Introduce `ha`. Use `⟨_, ha, ?_⟩` and prove the remaining obligations. Use `(Module.Basis.mk hli hsp.ge).sum_repr x` as an intermediate fact. Simplify using `only [Module.Basis.coe_mk] at this`. Conclude with `this.symm`.
-/
theorem exists_basis (hv : ∀ c, c ∈ RC ↔ v c ≤ 1) {V : Type} [AddCommGroup V] [Module C V] {r : ℕ}
    {L : AddSubgroup V} (h : LocFree RC r L) :
    ∃ e : Module.Basis (Fin r) C V, ∀ x, x ∈ L ↔ ∀ k, e.repr x k ∈ RC := by
  obtain ⟨hst, k, f, c, hf, hc, hsum, hb⟩ := h
  obtain ⟨l, hl⟩ : ∃ l, v (f l) = 1 := by
    by_contra hne
    push Not at hne
    have : v (∑ l, c l * f l) < 1 := by
      refine v.map_sum_lt one_ne_zero fun l _ => ?_
      rw [map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_right ((hv _).1 (hc l)) zero_le
        (lt_of_le_of_ne ((hv _).1 (hf l)) (hne l))
    rw [hsum, map_one] at this
    exact lt_irrefl _ this
  have hf0 : f l ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hl
    exact zero_ne_one hl
  obtain ⟨b, hli, hsp, hb⟩ := hb l
  refine ⟨Module.Basis.mk hli hsp.ge, fun x => ?_⟩
  have h₁ : (∃ n : ℕ, f l ^ n • x ∈ L) ↔ x ∈ L := by
    refine ⟨fun ⟨n, hn⟩ => ?_, fun hx => ⟨0, by simpa using hx⟩⟩
    have := hst (f l ^ n)⁻¹ ((hv _).2 (by simp [hl])) _ hn
    rwa [inv_smul_smul₀ (pow_ne_zero _ hf0)] at this
  have h₂ : ∀ t : C, (∃ n : ℕ, f l ^ n * t ∈ RC) ↔ t ∈ RC := fun t => by
    simp [hv, hl]
  rw [← h₁, hb]
  simp only [h₂]
  constructor
  · rintro ⟨a, ha, rfl⟩ q
    have := (Module.Basis.mk hli hsp.ge).repr_sum_self a
    simp only [Module.Basis.coe_mk] at this
    rw [this]
    exact ha q
  · intro ha
    refine ⟨_, ha, ?_⟩
    have := (Module.Basis.mk hli hsp.ge).sum_repr x
    simp only [Module.Basis.coe_mk] at this
    exact this.symm

/- English proof (translation)
Establish `h : ∀ k, ∃ N : ℕ, w ^ N * a k ∈ RC` using `fun k => by`. Distinguish the cases in `h0 : v (a k) = 0`. Conclude with `⟨0, (hv _).2 (by simp [h0])⟩`. Take `⟨N, hN⟩` from `exists_pow_lt_of_lt_one (inv_pos.2 (pos_iff_ne_zero.2 h0)) hw`. Use `⟨N, (hv _).2 ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, map_pow]`. Combine the equalities or inequalities in the displayed calculation. Use `choose N hN using h`. Use `⟨∑ k, N k, fun k => ?_⟩` and prove the remaining obligations. Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_le (Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))`.

Rewrite using `[hd, pow_add, mul_comm (w ^ N k), _root_.mul_assoc]`. Conclude with `RC.mul_mem (RC.pow_mem ((hv _).2 hw.le) _) (hN k)`.
-/
theorem exists_pow_mem (hv : ∀ c, c ∈ RC ↔ v c ≤ 1) {w : C} (hw : v w < 1) {κ : Type} [Fintype κ]
    (a : κ → C) : ∃ N : ℕ, ∀ k, w ^ N * a k ∈ RC := by
  have h : ∀ k, ∃ N : ℕ, w ^ N * a k ∈ RC := fun k => by
    by_cases h0 : v (a k) = 0
    · exact ⟨0, (hv _).2 (by simp [h0])⟩
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (pos_iff_ne_zero.2 h0)) hw
    refine ⟨N, (hv _).2 ?_⟩
    rw [map_mul, map_pow]
    calc v w ^ N * v (a k) ≤ (v (a k))⁻¹ * v (a k) := by gcongr
      _ = 1 := inv_mul_cancel₀ h0
  choose N hN using h
  refine ⟨∑ k, N k, fun k => ?_⟩
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le
    (Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
  rw [hd, pow_add, mul_comm (w ^ N k), _root_.mul_assoc]
  exact RC.mul_mem (RC.pow_mem ((hv _).2 hw.le) _) (hN k)

/- English proof (translation)
Rewrite using `[← e.sum_repr x, map_sum]`. Conclude with `M.sum_mem fun k _ => by rw [map_smul]; exact hM _ (hx k) _ (hT k)`.
-/
theorem mem_of_basis {V Z : Type} [AddCommGroup V] [Module C V] [AddCommGroup Z] [Module C Z] {r : ℕ}
    (e : Module.Basis (Fin r) C V) (T : V →ₗ[C] Z) (M : AddSubgroup Z)
    (hM : ∀ a ∈ RC, ∀ z ∈ M, a • z ∈ M) (hT : ∀ k, T (e k) ∈ M) (x : V) (hx : ∀ k, e.repr x k ∈ RC) :
    T x ∈ M := by
  rw [← e.sum_repr x, map_sum]
  exact M.sum_mem fun k _ => by rw [map_smul]; exact hM _ (hx k) _ (hT k)

/- English proof (translation)
Take `⟨g, hg⟩` from `exists_basis hv hom`. Set `N : Submodule RC (Fin s → C)` to `{ toAddSubmonoid := om.toAddSubmonoid smul_mem' := fun c x hx => hom.1 c c.2 x hx }`. Set `N' : Submodule RC (Fin s → C)` to `{ toAddSubmonoid := ((stdLat RC (Fin n)).map q.toAddMonoidHom).toAddSubmonoid smul_mem' := by`. Introduce and unpack `c _ ⟨x, hx, rfl⟩`. Conclude with `⟨(c : C) • x, std_smul c.2 hx, map_smul q (c : C) x⟩ }`.

Establish `hN : N = Submodule.span RC (Set.range g)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Rewrite using `[← g.sum_repr x]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ (⟨_, (hg x).1 hx k⟩ : RC) (Submodule.subset_span ⟨k, rfl⟩)`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Use `(hg _).2 fun j => ?_` and prove the remaining obligations. Rewrite using `[g.repr_self, Finsupp.single_apply]`. Use `split_ifs`.

Conclude with `RC.one_mem`. Conclude with `RC.zero_mem`. Establish `hfg : N.FG` using `hN ▸ Submodule.fg_span (Set.finite_range _)`. Set `w₀ : RC` to `⟨w, (hv _).2 hw.le⟩`. Establish `hj : Ideal.span {w₀} ≤ Ideal.jacobson ⊥`.

Rewrite using `[Ideal.span_singleton_le_iff_mem, Ideal.mem_jacobson_bot]`. Introduce `y`. Establish `h1 : v (w * y) < 1`. Rewrite using `[map_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left zero_le hw ((hv _).1 y.2)`.

Establish `h2 : v (w * y + 1) = 1` using `by rw [add_comm]; exact v.map_one_add_of_lt h1`. Establish `h3 : w * y + 1 ≠ 0`. Introduce `h0`. Rewrite `h2` using `[h0, map_zero]`. Conclude with `zero_ne_one h2`.

Use `IsUnit.of_mul_eq_one (⟨(w * y + 1)⁻¹, (hv _).2 (by simp [h2])⟩ : RC) (Subtype.ext ?_)` and prove the remaining obligations. Conclude with `mul_inv_cancel₀ h3`. Establish `hle : N ≤ N'`. Use `Submodule.le_of_le_smul_of_le_jacobson_bot hfg hj fun z hz => ?_` and prove the remaining obligations. Take `⟨b, hb, z', hz', rfl⟩` from `h z hz`.

Conclude with `Submodule.add_mem_sup ⟨b, hb, rfl⟩ (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self w₀) hz')`. Introduce `z hz`. Conclude with `hle hz`.
-/
theorem onto_of_mod (hv : ∀ c, c ∈ RC ↔ v c ≤ 1) {w : C} (hw : v w < 1) {s n : ℕ}
    {om : AddSubgroup (Fin s → C)} (hom : LocFree RC s om) (q : (Fin n → C) →ₗ[C] (Fin s → C))
    (h : ∀ z ∈ om, ∃ b ∈ stdLat RC (Fin n), ∃ z' ∈ om, z = q b + w • z') :
    ∀ z ∈ om, ∃ b ∈ stdLat RC (Fin n), q b = z := by
  obtain ⟨g, hg⟩ := exists_basis hv hom
  let N : Submodule RC (Fin s → C) :=
    { toAddSubmonoid := om.toAddSubmonoid
      smul_mem' := fun c x hx => hom.1 c c.2 x hx }
  let N' : Submodule RC (Fin s → C) :=
    { toAddSubmonoid := ((stdLat RC (Fin n)).map q.toAddMonoidHom).toAddSubmonoid
      smul_mem' := by
        rintro c _ ⟨x, hx, rfl⟩
        exact ⟨(c : C) • x, std_smul c.2 hx, map_smul q (c : C) x⟩ }
  have hN : N = Submodule.span RC (Set.range g) := by
    apply le_antisymm
    · intro x hx
      rw [← g.sum_repr x]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ (⟨_, (hg x).1 hx k⟩ : RC)
        (Submodule.subset_span ⟨k, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      refine (hg _).2 fun j => ?_
      rw [g.repr_self, Finsupp.single_apply]
      split_ifs
      · exact RC.one_mem
      · exact RC.zero_mem
  have hfg : N.FG := hN ▸ Submodule.fg_span (Set.finite_range _)
  let w₀ : RC := ⟨w, (hv _).2 hw.le⟩
  have hj : Ideal.span {w₀} ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_jacobson_bot]
    intro y
    have h1 : v (w * y) < 1 := by
      rw [map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hw ((hv _).1 y.2)
    have h2 : v (w * y + 1) = 1 := by rw [add_comm]; exact v.map_one_add_of_lt h1
    have h3 : w * y + 1 ≠ 0 := by
      intro h0
      rw [h0, map_zero] at h2
      exact zero_ne_one h2
    refine IsUnit.of_mul_eq_one (⟨(w * y + 1)⁻¹, (hv _).2 (by simp [h2])⟩ : RC) (Subtype.ext ?_)
    exact mul_inv_cancel₀ h3
  have hle : N ≤ N' := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot hfg hj fun z hz => ?_
    obtain ⟨b, hb, z', hz', rfl⟩ := h z hz
    exact Submodule.add_mem_sup ⟨b, hb, rfl⟩
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self w₀) hz')
  intro z hz
  exact hle hz

/- English proof (translation)
Establish `hwR : w ∈ RC` using `(hv _).2 hw.le`. Establish `hi : ∀ a ∈ W, i a ∈ stdLat RC (Fin n)` using `fun a ha => by`. Simplify using `using ((h₁ a).2 ha).2`. Establish `hq : ∀ b ∈ stdLat RC (Fin n), q b ∈ om` using `fun b hb => by`. Simplify `hb⟩).2` using `using ((h₃ b).2 ⟨0, by simp, by simpa`.

Establish `honto : ∀ z ∈ om, ∃ b ∈ stdLat RC (Fin n), q b = z`. Use `onto_of_mod hv hw hom q fun z hz => ?_` and prove the remaining obligations. Take `⟨b, hb, hc⟩` from `(h₂ (w⁻¹ • z)).2 (by rwa [smul_inv_smul₀ hw0])`. Use `⟨_, hb, _, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_sub, smul_inv_smul₀ hw0, map_smul]`.

Normalize the expressions using the abelian group laws. Take `⟨e, he⟩` from `exists_basis hv hW`. Establish `heW : ∀ k, e k ∈ W` using `fun k => (he _).2 fun j => by`. Rewrite using `[e.repr_self, Finsupp.single_apply]`. Use `split_ifs`.

Conclude with `RC.one_mem`. Conclude with `RC.zero_mem`. Establish `hk : ∀ k, ∃ b ∈ stdLat RC (Fin n), q b = q (i (w⁻¹ • e k))` using `fun k => by`. Use `honto _ ?_` and prove the remaining obligations. Simplify `((h₃ (i (w⁻¹ • e k))).2 ⟨w⁻¹ • e k, by rw [smul_inv_smul₀ hw0]; exact heW k, by simp⟩).2` using `only [zero_sub, neg_mem_iff]`.

Use `choose b hb hqb using hk`. Set `β : (Fin r → C) →ₗ[C] (Fin n → C)` to `e.constr C b`. Establish `hβ : ∀ a ∈ W, β a ∈ stdLat RC (Fin n)` using `fun a ha => mem_of_basis e β _ (fun _ hc _ hz => std_smul hc hz) (fun k => by simpa [β] using hb k) a ((he a).1 ha)`. Establish `hcomp : q ∘ₗ (i - w • β) = 0` using `e.ext fun k => by`. Establish `: β (e k) = b k` using `by simp [β]`.

Simplify using `[this, hqb, smul_inv_smul₀ hw0]`. Establish `hd : ∀ a, (i - w • β) a - i a = -β (w • a)` using `fun a => by simp`. Establish `hstep : ∀ a, (i - w • β) a ∈ stdLat RC (Fin n) → w • a ∈ W → a ∈ W` using `fun a ha hwa => by`. Use `(h₁ a).1 ⟨hwa, ?_⟩` and prove the remaining obligations. Use `(stdLat RC (Fin n)).sub_mem ((stdLat RC (Fin n)).neg_mem (hβ _ hwa)) ha` as an intermediate fact.

Rewrite `this` using `[← hd]`. Simplify `this` using `only [zero_sub, sub_sub_cancel_left]`. Establish `hcm : ∀ a, (i - w • β) a ∈ stdLat RC (Fin n) → a ∈ W` using `fun a ha => by`. Take `⟨N, hN⟩` from `exists_pow_mem hv hw (e.repr a)`. Establish `h0 : w ^ N • a ∈ W` using `(he _).2 fun k => by simpa using hN k`.

Use `clear hN`. Proceed by induction on `N with`. Consider the case `zero => simpa using h0`. Consider the case `succ N ih`. Use `ih (hstep _ ?_ (by rwa [← mul_smul, ← pow_succ']))` and prove the remaining obligations.

Rewrite using `[map_smul]`. Conclude with `std_smul (RC.pow_mem hwR _) ha`. Establish `hinj : Function.Injective (i - w • β)`. Use `(injective_iff_map_eq_zero _).2 fun a ha => ?_` and prove the remaining obligations. Use `e.repr.injective (Finsupp.ext fun k => ?_)` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Establish `hne' : e.repr a k ≠ 0` using `by simpa using hne`. Establish `h` using `(he _).1 (hcm ((w * e.repr a k)⁻¹ • a) (by rw [map_smul, ha, smul_zero]; exact zero_mem _)) k`. Establish `h' : w⁻¹ ∈ RC`. Use `h using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [map_smul, Finsupp.smul_apply, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Use `(hv _).1 h'` as an intermediate fact. Rewrite `this` using `[map_inv₀, inv_le_one₀ (pos_iff_ne_zero.2 (by simpa using hw0))]`. Conclude with `absurd hw (not_lt.2 this)`.

Establish `hsurj : LinearMap.range q = ⊤`. Take `⟨g, hg⟩` from `exists_basis hv hom`. Rewrite using `[eq_top_iff, ← g.span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Take `⟨x, -, hx⟩` from `honto (g k) ((hg _).2 fun j => by`.

Rewrite using `[g.repr_self, Finsupp.single_apply]`. Use `split_ifs`. Conclude with `RC.one_mem`. Conclude with `RC.zero_mem)`. Conclude with `⟨x, hx⟩`.

Use `⟨i - w • β, hinj, ?_, ?_, ?_, fun a ha => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Use `Submodule.eq_of_le_of_finrank_eq (LinearMap.range_le_ker_iff.2 hcomp) ?_` and prove the remaining obligations. Establish `h` using `q.finrank_range_add_finrank_ker`. Rewrite `h` using `[hsurj, finrank_top]`. Rewrite using `[LinearMap.finrank_range_of_inj hinj]`.

Simplify using `only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h ⊢`. Use linear arithmetic over natural numbers and integers. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `hq x hx`.

Introduce `z hz`. Conclude with `honto z hz`. Use extensionality with `a`. Use `⟨hcm a, fun ha => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `i a - w • β a ∈ stdLat RC (Fin n)`.

Conclude with `AddSubgroup.sub_mem _ (hi a ha) (std_smul hwR (hβ a ha))`. Rewrite using `[hd]`. Conclude with `AddSubgroup.neg_mem _ (hβ _ ha)`. Conclude with `⟨-β a, AddSubgroup.neg_mem _ (hβ _ ha), by simp⟩`.
-/
theorem exists_lift (hv : ∀ c, c ∈ RC ↔ v c ≤ 1) {w : C} (hw : v w < 1) (hw0 : w ≠ 0) {r s n : ℕ}
    (hrs : r + s = n) {W : AddSubgroup (Fin r → C)} {om : AddSubgroup (Fin s → C)}
    (hW : LocFree RC r W) (hom : LocFree RC s om)
    (i : (Fin r → C) →ₗ[C] (Fin n → C)) (q : (Fin n → C) →ₗ[C] (Fin s → C))
    (h₁ : ∀ a, (w • a ∈ W ∧ 0 - i a ∈ stdLat RC (Fin n)) ↔ a ∈ W)
    (h₂ : ∀ c, (∃ b, w • b ∈ stdLat RC (Fin n) ∧ c - q b ∈ om) ↔ w • c ∈ om)
    (h₃ : ∀ b, (w • b ∈ stdLat RC (Fin n) ∧ 0 - q b ∈ om) ↔
      ∃ a, w • a ∈ W ∧ b - i a ∈ stdLat RC (Fin n)) :
    ∃ hb : (Fin r → C) →ₗ[C] (Fin n → C), Function.Injective hb ∧
      LinearMap.range hb = LinearMap.ker q ∧ (stdLat RC _).map q.toAddMonoidHom = om ∧
      (stdLat RC _).comap hb.toAddMonoidHom = W ∧
      (∀ a, w • a ∈ W → hb a - i a ∈ stdLat RC _) ∧
      ∀ a ∈ W, hb a - i a ∈ mulLat w (stdLat RC _) := by
  have hwR : w ∈ RC := (hv _).2 hw.le
  have hi : ∀ a ∈ W, i a ∈ stdLat RC (Fin n) := fun a ha => by
    simpa using ((h₁ a).2 ha).2
  have hq : ∀ b ∈ stdLat RC (Fin n), q b ∈ om := fun b hb => by
    simpa using ((h₃ b).2 ⟨0, by simp, by simpa using hb⟩).2
  have honto : ∀ z ∈ om, ∃ b ∈ stdLat RC (Fin n), q b = z := by
    refine onto_of_mod hv hw hom q fun z hz => ?_
    obtain ⟨b, hb, hc⟩ := (h₂ (w⁻¹ • z)).2 (by rwa [smul_inv_smul₀ hw0])
    refine ⟨_, hb, _, hc, ?_⟩
    rw [smul_sub, smul_inv_smul₀ hw0, map_smul]
    abel
  obtain ⟨e, he⟩ := exists_basis hv hW
  have heW : ∀ k, e k ∈ W := fun k => (he _).2 fun j => by
    rw [e.repr_self, Finsupp.single_apply]
    split_ifs
    · exact RC.one_mem
    · exact RC.zero_mem
  have hk : ∀ k, ∃ b ∈ stdLat RC (Fin n), q b = q (i (w⁻¹ • e k)) := fun k => by
    refine honto _ ?_
    simpa only [zero_sub, neg_mem_iff] using ((h₃ (i (w⁻¹ • e k))).2 ⟨w⁻¹ • e k,
      by rw [smul_inv_smul₀ hw0]; exact heW k, by simp⟩).2
  choose b hb hqb using hk
  let β : (Fin r → C) →ₗ[C] (Fin n → C) := e.constr C b
  have hβ : ∀ a ∈ W, β a ∈ stdLat RC (Fin n) := fun a ha =>
    mem_of_basis e β _ (fun _ hc _ hz => std_smul hc hz) (fun k => by simpa [β] using hb k) a
      ((he a).1 ha)
  have hcomp : q ∘ₗ (i - w • β) = 0 := e.ext fun k => by
    have : β (e k) = b k := by simp [β]
    simp [this, hqb, smul_inv_smul₀ hw0]
  have hd : ∀ a, (i - w • β) a - i a = -β (w • a) := fun a => by simp
  have hstep : ∀ a, (i - w • β) a ∈ stdLat RC (Fin n) → w • a ∈ W → a ∈ W := fun a ha hwa => by
    refine (h₁ a).1 ⟨hwa, ?_⟩
    have := (stdLat RC (Fin n)).sub_mem ((stdLat RC (Fin n)).neg_mem (hβ _ hwa)) ha
    rw [← hd] at this
    simpa only [zero_sub, sub_sub_cancel_left] using this
  have hcm : ∀ a, (i - w • β) a ∈ stdLat RC (Fin n) → a ∈ W := fun a ha => by
    obtain ⟨N, hN⟩ := exists_pow_mem hv hw (e.repr a)
    have h0 : w ^ N • a ∈ W := (he _).2 fun k => by simpa using hN k
    clear hN
    induction N with
    | zero => simpa using h0
    | succ N ih =>
      refine ih (hstep _ ?_ (by rwa [← mul_smul, ← pow_succ']))
      rw [map_smul]
      exact std_smul (RC.pow_mem hwR _) ha
  have hinj : Function.Injective (i - w • β) := by
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    refine e.repr.injective (Finsupp.ext fun k => ?_)
    by_contra hne
    have hne' : e.repr a k ≠ 0 := by simpa using hne
    have h := (he _).1 (hcm ((w * e.repr a k)⁻¹ • a) (by rw [map_smul, ha, smul_zero]; exact zero_mem _)) k
    have h' : w⁻¹ ∈ RC := by
      convert h using 1
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
      field_simp
    have := (hv _).1 h'
    rw [map_inv₀, inv_le_one₀ (pos_iff_ne_zero.2 (by simpa using hw0))] at this
    exact absurd hw (not_lt.2 this)
  have hsurj : LinearMap.range q = ⊤ := by
    obtain ⟨g, hg⟩ := exists_basis hv hom
    rw [eq_top_iff, ← g.span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    obtain ⟨x, -, hx⟩ := honto (g k) ((hg _).2 fun j => by
      rw [g.repr_self, Finsupp.single_apply]
      split_ifs
      · exact RC.one_mem
      · exact RC.zero_mem)
    exact ⟨x, hx⟩
  refine ⟨i - w • β, hinj, ?_, ?_, ?_, fun a ha => ?_, fun a ha => ?_⟩
  · refine Submodule.eq_of_le_of_finrank_eq (LinearMap.range_le_ker_iff.2 hcomp) ?_
    have h := q.finrank_range_add_finrank_ker
    rw [hsurj, finrank_top] at h
    rw [LinearMap.finrank_range_of_inj hinj]
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h ⊢
    omega
  · apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hq x hx
    · intro z hz
      exact honto z hz
  · ext a
    refine ⟨hcm a, fun ha => ?_⟩
    change i a - w • β a ∈ stdLat RC (Fin n)
    exact AddSubgroup.sub_mem _ (hi a ha) (std_smul hwR (hβ a ha))
  · rw [hd]
    exact AddSubgroup.neg_mem _ (hβ _ ha)
  · exact ⟨-β a, AddSubgroup.neg_mem _ (hβ _ ha), by simp⟩

end Val

end PositivityTheory.Xgn.TestLift

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d _ _ p hp _ _ _ _ b _ φ _ A _ _ _ m _ _ O _ _ _ _ _ _ _ t₀ Sg _ e φ' F _ _ _ pq sc w σ horb _ G c' _ P i _ hbase C _ _ _ _ RC htest χ _ τ`. Take `⟨-, -, -, -, -, -, ⟨hp0, ⟨u, hu, hwu⟩, -⟩, -⟩` from `horb`. Take `⟨-, ⟨v, hv, hvp⟩, -, hR⟩` from `htest`. Establish `hp2` using `hp.out.two_le`. Establish `hpΩ : (p : Ω) ≠ 0`.

Introduce `h`. Establish `hA : (p : A) = 0` using `IsIntegralClosure.algebraMap_injective A ℤ Ω (by simpa using h)`. Apply `hp0` to reduce the goal to its premises. Rewrite using `[← map_natCast (algebraMap A O), hA, map_zero]`. Take `⟨u', hu'⟩` from `hu.exists_left_inv`.

Establish `hpw : (p : O) = (u' * w ^ (p - 2)) * w`. Establish `: p - 1 = p - 2 + 1` using `by omega`. Rewrite using `[_root_.mul_assoc, ← pow_succ, ← this, hwu, ← _root_.mul_assoc, hu', _root_.one_mul]`. Establish `hpwΩ : (p : Ω) = algebraMap O Ω (u' * w ^ (p - 2)) * algebraMap O Ω w`. Rewrite using `[← map_mul, ← hpw, map_natCast]`.

Establish `hw0 : algebraMap O Ω w ≠ 0`. Introduce `h`. Rewrite `hpwΩ` using `[h, mul_zero]`. Conclude with `hpΩ hpwΩ`. Establish `hcd : CharData (CR O y c') p (algebraMap O Ω w) (fun (_ : Sg) (a : F) => if a = 0 then (0 : Ω) else 1)`.

Use `⟨hpΩ, Subalgebra.algebraMap_mem _ _, ⟨_, Subalgebra.algebraMap_mem _ _, hpwΩ⟩, zero_ne_one, fun _ => ⟨by simp, by simp, fun a => ?_⟩⟩` and prove the remaining obligations. Simplify using `only`. Use `split_ifs`. Conclude with `zero_mem _`. Conclude with `one_mem _`.

Establish `hB` using `(PositivityTheory.Xgn.character_data_base_change _ _ p _ _ hcd hbase C RC hR).2`. Establish `hwC : algebraMap Ω C (algebraMap O Ω w) = algebraMap O C w` using `(IsScalarTower.algebraMap_apply _ _ _ _).symm`. Establish `hwC0 : algebraMap O C w ≠ 0`. Rewrite using `[← hwC]`. Simplify using `using hw0`.

Establish `hvw : v (algebraMap O C w) < 1`. Assume the negation of the conclusion as `hge`. Establish `h1 : 1 ≤ v (algebraMap O C w) ^ (p - 1)` using `one_le_pow₀ (not_lt.1 hge)`. Rewrite `h1` using `[← map_pow, ← map_pow, hwu, map_mul, map_mul, map_natCast]`. Conclude with `absurd (mul_lt_one_of_nonneg_of_lt_one_right ((hv _).1 (RC.algebraMap_mem u)) zero_le hvp) (not_lt.2 h1)`.

Establish `hstd` using `PositivityTheory.Xgn.LocallyFreeLatticeSpans.span_std RC (CR O y c') hR (Fin (D.p + D.q))`. Establish `hDel : ∀ b' c'', (b', c'') ∈ ((chartD e b pq sc w P i).bc RC).Del τ ↔ (algebraMap O C w) • b' ∈ stdLat RC _ ∧ c'' - (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) b' ∈ ((chartD e b pq sc w P i).bc RC).omHT τ` using `fun b' c'' => by`. Rewrite using `[← hstd, ← hwC]`. Conclude with `PositivityTheory.Xgn.TestLift.graph_bc RC hw0 _ _ _ _ (fun _ => Iff.rfl) b' c''`. Establish `hGam : ∀ a b', (a, b') ∈ ((chartD e b pq sc w P i).bc RC).Gam τ ↔ (algebraMap O C w) • a ∈ ((chartD e b pq sc w P i).bc RC).W τ ∧ b' - GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (i τ) a ∈ stdLat RC _` using `fun a b' => by`.

Rewrite using `[← hstd, ← hwC]`. Conclude with `PositivityTheory.Xgn.TestLift.graph_bc RC hw0 _ _ _ _ (fun _ => Iff.rfl) a b'`. Establish `hrs : labelRk D (e τ) + labelRk D (e τ).swap = D.p + D.q`. Break down `e τ with t | t` into its components or cases. Both sides reduce to the same expression.

Conclude with `Nat.add_comm _ _`. Rewrite `hB` using `[hwC]`. Take `⟨hb, h1, h2, h3, h4, h5, h6⟩` from `PositivityTheory.Xgn.TestLift.exists_lift hv hvw hwC0 hrs (hB.free τ).2.1 (hB.free τ).2.2.2 (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (i τ)) (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) (fun a => by rw [← hGam]; exact (hB.gam …`. Use `⟨hb, h1, h2, h3, h4, hDel, fun a b' => ?_, h6⟩` and prove the remaining obligations. Rewrite using `[hGam]`.

Use `and_congr_right fun ha => ⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Simplify `AddSubgroup.sub_mem _ h (h5 a ha)` using `only [sub_sub_sub_cancel_right]`. Simplify `AddSubgroup.add_mem _ h (h5 a ha)` using `only [sub_add_sub_cancel]`.
-/
theorem PositivityTheory.Xgn.test_lift_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ τ, ∃ hb : ((Fin (labelRk D (e τ)) → C) →ₗ[C] (Fin (D.p + D.q) → C)), Function.Injective hb ∧ LinearMap.range hb = LinearMap.ker (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) ∧ (stdLat RC _).map (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))).toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).omHT τ ∧ (stdLat RC _).comap hb.toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).W τ ∧ (∀ b' c'', (b', c'') ∈ ((chartD e b pq sc w P i).bc RC).Del τ ↔ (algebraMap O C w) • b' ∈ stdLat RC _ ∧ c'' - (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) b' ∈ ((chartD e b pq sc w P i).bc RC).omHT τ) ∧ (∀ a b', (a, b') ∈ ((chartD e b pq sc w P i).bc RC).Gam τ ↔ (algebraMap O C w) • a ∈ ((chartD e b pq sc w P i).bc RC).W τ ∧ b' - hb a ∈ stdLat RC _) ∧ ∀ a ∈ ((chartD e b pq sc w P i).bc RC).W τ, hb a - GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (i τ) a ∈ mulLat (algebraMap O C w) (stdLat RC _) := by
  classical
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d _ _ p hp _ _ _ _ b _ φ _ A _ _ _ m _ _ O _ _ _ _ _ _ _
    t₀ Sg _ e φ' F _ _ _ pq sc w σ horb _ G c' _ P i _ hbase C _ _ _ _ RC htest χ _ τ
  obtain ⟨-, -, -, -, -, -, ⟨hp0, ⟨u, hu, hwu⟩, -⟩, -⟩ := horb
  obtain ⟨-, ⟨v, hv, hvp⟩, -, hR⟩ := htest
  have hp2 := hp.out.two_le
  have hpΩ : (p : Ω) ≠ 0 := by
    intro h
    have hA : (p : A) = 0 := IsIntegralClosure.algebraMap_injective A ℤ Ω (by simpa using h)
    apply hp0
    rw [← map_natCast (algebraMap A O), hA, map_zero]
  obtain ⟨u', hu'⟩ := hu.exists_left_inv
  have hpw : (p : O) = (u' * w ^ (p - 2)) * w := by
    have : p - 1 = p - 2 + 1 := by omega
    rw [_root_.mul_assoc, ← pow_succ, ← this, hwu, ← _root_.mul_assoc, hu', _root_.one_mul]
  have hpwΩ : (p : Ω) = algebraMap O Ω (u' * w ^ (p - 2)) * algebraMap O Ω w := by
    rw [← map_mul, ← hpw, map_natCast]
  have hw0 : algebraMap O Ω w ≠ 0 := by
    intro h
    rw [h, mul_zero] at hpwΩ
    exact hpΩ hpwΩ
  have hcd : CharData (CR O y c') p (algebraMap O Ω w) (fun (_ : Sg) (a : F) => if a = 0 then (0 : Ω) else 1) := by
    refine ⟨hpΩ, Subalgebra.algebraMap_mem _ _, ⟨_, Subalgebra.algebraMap_mem _ _, hpwΩ⟩, zero_ne_one,
      fun _ => ⟨by simp, by simp, fun a => ?_⟩⟩
    dsimp only
    split_ifs
    · exact zero_mem _
    · exact one_mem _
  have hB := (PositivityTheory.Xgn.character_data_base_change _ _ p _ _ hcd hbase C RC hR).2
  have hwC : algebraMap Ω C (algebraMap O Ω w) = algebraMap O C w := (IsScalarTower.algebraMap_apply _ _ _ _).symm
  have hwC0 : algebraMap O C w ≠ 0 := by
    rw [← hwC]
    simpa using hw0
  have hvw : v (algebraMap O C w) < 1 := by
    by_contra hge
    have h1 : 1 ≤ v (algebraMap O C w) ^ (p - 1) := one_le_pow₀ (not_lt.1 hge)
    rw [← map_pow, ← map_pow, hwu, map_mul, map_mul, map_natCast] at h1
    exact absurd (mul_lt_one_of_nonneg_of_lt_one_right ((hv _).1 (RC.algebraMap_mem u)) zero_le hvp)
      (not_lt.2 h1)
  have hstd := PositivityTheory.Xgn.LocallyFreeLatticeSpans.span_std RC (CR O y c') hR (Fin (D.p + D.q))
  have hDel : ∀ b' c'', (b', c'') ∈ ((chartD e b pq sc w P i).bc RC).Del τ ↔
      (algebraMap O C w) • b' ∈ stdLat RC _ ∧ c'' - (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) b' ∈
        ((chartD e b pq sc w P i).bc RC).omHT τ := fun b' c'' => by
    rw [← hstd, ← hwC]
    exact PositivityTheory.Xgn.TestLift.graph_bc RC hw0 _ _ _ _ (fun _ => Iff.rfl) b' c''
  have hGam : ∀ a b', (a, b') ∈ ((chartD e b pq sc w P i).bc RC).Gam τ ↔
      (algebraMap O C w) • a ∈ ((chartD e b pq sc w P i).bc RC).W τ ∧
        b' - GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (i τ) a ∈ stdLat RC _ := fun a b' => by
    rw [← hstd, ← hwC]
    exact PositivityTheory.Xgn.TestLift.graph_bc RC hw0 _ _ _ _ (fun _ => Iff.rfl) a b'
  have hrs : labelRk D (e τ) + labelRk D (e τ).swap = D.p + D.q := by
    rcases e τ with t | t
    · rfl
    · exact Nat.add_comm _ _
  rw [hwC] at hB
  obtain ⟨hb, h1, h2, h3, h4, h5, h6⟩ := PositivityTheory.Xgn.TestLift.exists_lift hv hvw hwC0 hrs
    (hB.free τ).2.1 (hB.free τ).2.2.2 (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (i τ))
    (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap)))
    (fun a => by rw [← hGam]; exact (hB.gam τ).2.2 a)
    (fun z => by simp only [← hDel]; exact (hB.del τ).2.1 z)
    (fun z => by simp only [← hDel, ← hGam]; exact (hB.del τ).2.2.2 z)
  refine ⟨hb, h1, h2, h3, h4, hDel, fun a b' => ?_, h6⟩
  rw [hGam]
  refine and_congr_right fun ha => ⟨fun h => ?_, fun h => ?_⟩
  · simpa only [sub_sub_sub_cancel_right] using AddSubgroup.sub_mem _ h (h5 a ha)
  · simpa only [sub_add_sub_cancel] using AddSubgroup.add_mem _ h (h5 a ha)
