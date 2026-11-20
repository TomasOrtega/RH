import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.LinOn

/- English proof (translation)
Rewrite using `[← (TensorProduct.isBaseChange ℤ X ℚ).finrank_eq, ← (TensorProduct.isBaseChange (𝓞 E) X E).finrank_eq, Module.finrank_mul_finrank, (Algebra.IsPushout.cancelBaseChange ℤ ℚ (𝓞 E) E X).finrank_eq]`.
-/
theorem finrank_int_eq' (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X] :
    Module.finrank ℤ X = Module.finrank ℚ E * Module.finrank (𝓞 E) X := by
  rw [← (TensorProduct.isBaseChange ℤ X ℚ).finrank_eq, ← (TensorProduct.isBaseChange (𝓞 E) X E).finrank_eq,
    Module.finrank_mul_finrank, (Algebra.IsPushout.cancelBaseChange ℤ ℚ (𝓞 E) E X).finrank_eq]

variable {X : Type} [AddCommGroup X] {m : ℕ}

section Pol

variable [Module.Finite ℤ X]

/- English proof (translation)
Establish `hmem : ∀ d : Fin m → ℝ, (∀ i, 0 ≤ d i) → ∑ i, d i • toReal (γ i) ∈ psdCone (id : ℤ → ℤ) X` using `fun d hd => GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone ℤ id X m γ d h1 h2 hd`. Establish `hsub : ∀ s : Finset (Fin m), ∑ i ∈ s, c i • toReal (γ i) ∈ psdCone (id : ℤ → ℤ) X` using `fun s => by`. Use `hmem (fun i => if i ∈ s then c i else 0) fun i => by split_ifs` as an intermediate fact. Conclude with `hc i`. Conclude with `le_rfl`.

Simplify `this` using `[ite_smul, Finset.sum_ite_mem]`. Establish `hone : ∀ a, toReal (γ a) ∈ psdCone (id : ℤ → ℤ) X` using `fun a => by`. Use `hmem (Pi.single a 1) fun i => by` as an intermediate fact. Distinguish the cases in `e : i = a`. Substitute `e` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne e]`. Simplify `this` using `[Pi.single_apply, ite_smul]`. Establish `key : ∀ s : Finset (Fin m), ∑ i ∈ s, c i * φ.evalZ (γ i) ≤ evalR φ (∑ i ∈ s, c i • toReal (γ i))` using `fun s => by`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Use `le_trans ?_ (h.superadd _ (smul_mem_psdCone (hone a) (hc a)) _ (hsub s))` and prove the remaining obligations. Rewrite using `[h.homog _ (hone a) _ (hc a), evalR_toReal]`.

Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `using key Finset.univ`.
-/
theorem sum_le_evalR {φ : InvFun ℤ} (h : IsPolFanOn (id : ℤ → ℤ) φ X) {γ : Fin m → LinearMap.BilinForm ℤ X}
    (h1 : ∀ i, γ i ∈ balForms (id : ℤ → ℤ) X) (h2 : ∀ i y, 0 ≤ γ i y y) {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i) :
    ∑ i, c i * φ.evalZ (γ i) ≤ evalR φ (∑ i, c i • toReal (γ i)) := by
  classical
  have hmem : ∀ d : Fin m → ℝ, (∀ i, 0 ≤ d i) → ∑ i, d i • toReal (γ i) ∈ psdCone (id : ℤ → ℤ) X :=
    fun d hd => GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone ℤ id X m γ d h1 h2 hd
  have hsub : ∀ s : Finset (Fin m), ∑ i ∈ s, c i • toReal (γ i) ∈ psdCone (id : ℤ → ℤ) X := fun s => by
    have := hmem (fun i => if i ∈ s then c i else 0) fun i => by
      split_ifs
      · exact hc i
      · exact le_rfl
    simpa [ite_smul, Finset.sum_ite_mem] using this
  have hone : ∀ a, toReal (γ a) ∈ psdCone (id : ℤ → ℤ) X := fun a => by
    have := hmem (Pi.single a 1) fun i => by
      by_cases e : i = a
      · subst e; simp
      · simp [Pi.single_eq_of_ne e]
    simpa [Pi.single_apply, ite_smul] using this
  have key : ∀ s : Finset (Fin m), ∑ i ∈ s, c i * φ.evalZ (γ i) ≤ evalR φ (∑ i ∈ s, c i • toReal (γ i)) := fun s => by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      refine le_trans ?_ (h.superadd _ (smul_mem_psdCone (hone a) (hc a)) _ (hsub s))
      rw [h.homog _ (hone a) _ (hc a), evalR_toReal]
      linarith
  simpa using key Finset.univ

end Pol

section Mean

variable (M : ℕ) {k : ℕ} {s : (Fin k → ℤ) →ₗ[ℤ] X}

abbrev rd (s : (Fin k → ℤ) →ₗ[ℤ] X) (B : X → X → ℝ) : (Fin k → ℤ) → (Fin k → ℤ) → ℝ := fun a b => B (s a) (s b)

/- English proof (translation)
Rewrite using `[InvFun.eval_eq _ hs]`. Simplify using `[fineMean]`.
-/
theorem fineMean_eval [Module.Finite ℤ X] (hs : Function.Surjective s) (B : X → X → ℝ) :
    (fineMean M).eval X B = (((M : ℝ) + 1) ^ k)⁻¹ * ∑ y, classMin M (rd s B) y - B 0 0 := by
  rw [InvFun.eval_eq _ hs]
  simp [fineMean]

/- English proof (translation)
Use `csInf_le ⟨0, ?_⟩ ⟨a, rfl, rfl⟩` and prove the remaining obligations. Introduce and unpack `x ⟨a, -, rfl⟩`. Use `show (0 : ℝ) ≤ ((β (s a) (s a) : ℤ) : ℝ)`. Conclude with `h (s a)` after adjusting the coercions.
-/
theorem classMin_le {β : LinearMap.BilinForm ℤ X} (h : ∀ y, 0 ≤ β y y) (s : (Fin k → ℤ) →ₗ[ℤ] X) (a : Fin k → ℤ) :
    classMin M (rd s fun a b => (β a b : ℝ)) (redV M a) ≤ (β (s a) (s a) : ℝ) := by
  refine csInf_le ⟨0, ?_⟩ ⟨a, rfl, rfl⟩
  rintro x ⟨a, -, rfl⟩
  show (0 : ℝ) ≤ ((β (s a) (s a) : ℤ) : ℝ)
  exact_mod_cast h (s a)

/- English proof (translation)
Take `⟨a₀, ha₀⟩` from `redV_surjective M k y`. Use `le_csInf ⟨_, a₀, ha₀, rfl⟩ ?_` and prove the remaining obligations. Introduce and unpack `x ⟨a, rfl, rfl⟩`. Conclude with `Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (classMin_le M (h i) s a) (hc i)`.
-/
theorem sum_classMin_le {γ : Fin m → LinearMap.BilinForm ℤ X} (h : ∀ i y, 0 ≤ γ i y y) (s : (Fin k → ℤ) →ₗ[ℤ] X)
    {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i) (y : Fin k → ZMod (M + 1)) :
    ∑ i, c i * classMin M (rd s fun a b => (γ i a b : ℝ)) y ≤
      classMin M (rd s fun a b => ∑ i, c i * (γ i a b : ℝ)) y := by
  obtain ⟨a₀, ha₀⟩ := redV_surjective M k y
  refine le_csInf ⟨_, a₀, ha₀, rfl⟩ ?_
  rintro x ⟨a, rfl, rfl⟩
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (classMin_le M (h i) s a) (hc i)

/- English proof (translation)
Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem sum_mul_mean {Y : Type} [Fintype Y] (K : ℝ) (c : Fin m → ℝ) (f : Fin m → Y → ℝ) :
    ∑ i, c i * (K * ∑ y, f i y) = K * ∑ y, ∑ i, c i * f i y := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Check the signs of the components of the expression.
-/
theorem mean_pos : (0 : ℝ) < (((M : ℝ) + 1) ^ k)⁻¹ := by positivity

/- English proof (translation)
Rewrite using `[InvFun.evalZ, fineMean_eval M hs]`. Simplify using the standard rewrite rules.
-/
theorem fineMean_evalZ [Module.Finite ℤ X] (hs : Function.Surjective s) (β : LinearMap.BilinForm ℤ X) :
    (fineMean M).evalZ β = (((M : ℝ) + 1) ^ k)⁻¹ * ∑ y, classMin M (rd s fun a b => (β a b : ℝ)) y := by
  rw [InvFun.evalZ, fineMean_eval M hs]
  simp

/- English proof (translation)
Rewrite using `[fineMean_eval M hs]`. Simplify using the standard rewrite rules.
-/
theorem fineMean_evalSum [Module.Finite ℤ X] (hs : Function.Surjective s) (γ : Fin m → LinearMap.BilinForm ℤ X)
    (c : Fin m → ℝ) :
    (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) =
      (((M : ℝ) + 1) ^ k)⁻¹ * ∑ y, classMin M (rd s fun a b => ∑ i, c i * (γ i a b : ℝ)) y := by
  rw [fineMean_eval M hs]
  simp

/- English proof (translation)
Take `⟨k, s, hs⟩` from `Module.Finite.exists_fin' ℤ X`. Rewrite using `[fineMean_evalSum M hs]`. Simplify using `only [fineMean_evalZ M hs]`. Rewrite using `[sum_mul_mean]`. Conclude with `mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => sum_classMin_le M h s hc y) (mean_pos M).le`.
-/
theorem sum_fineMean_le [Module.Finite ℤ X] {γ : Fin m → LinearMap.BilinForm ℤ X} (h : ∀ i y, 0 ≤ γ i y y)
    {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i) :
    ∑ i, c i * (fineMean M).evalZ (γ i) ≤ (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) := by
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin' ℤ X
  rw [fineMean_evalSum M hs]
  simp only [fineMean_evalZ M hs]
  rw [sum_mul_mean]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => sum_classMin_le M h s hc y) (mean_pos M).le

/- English proof (translation)
Rewrite `he` using `[fineMean_evalSum M hs]`. Simplify using `only [fineMean_evalZ M hs] at he`. Rewrite `he` using `[sum_mul_mean]`. Establish `e3` using `mul_left_cancel₀ (mean_pos (k := k) M).ne' he`. Use `(Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (f := fun y => ∑ i, (1 : ℝ) * classMin M (rd s fun a b => (γ i a b : ℝ)) y) (g := fun y => classMin M (rd s fun a b => ∑ i, (1 : ℝ) * (γ i a b : ℝ)) y) fun y _ => sum_classMin_le M h s (fun _ => zero_le_one) y).1 e3.symm y (Finset.m …` as an intermediate fact.

Conclude with `this.symm`.
-/
theorem classMin_sum_eq [Module.Finite ℤ X] {γ : Fin m → LinearMap.BilinForm ℤ X} (h : ∀ i y, 0 ≤ γ i y y)
    (hs : Function.Surjective s)
    (he : (fineMean M).eval X (fun a b => ∑ i, (1 : ℝ) * (γ i a b : ℝ)) = ∑ i, (1 : ℝ) * (fineMean M).evalZ (γ i))
    (y : Fin k → ZMod (M + 1)) :
    classMin M (rd s fun a b => ∑ i, (1 : ℝ) * (γ i a b : ℝ)) y =
      ∑ i, (1 : ℝ) * classMin M (rd s fun a b => (γ i a b : ℝ)) y := by
  rw [fineMean_evalSum M hs] at he
  simp only [fineMean_evalZ M hs] at he
  rw [sum_mul_mean] at he
  have e3 := mul_left_cancel₀ (mean_pos (k := k) M).ne' he
  have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
    (f := fun y => ∑ i, (1 : ℝ) * classMin M (rd s fun a b => (γ i a b : ℝ)) y)
    (g := fun y => classMin M (rd s fun a b => ∑ i, (1 : ℝ) * (γ i a b : ℝ)) y)
    fun y _ => sum_classMin_le M h s (fun _ => zero_le_one) y).1 e3.symm y (Finset.mem_univ y)
  exact this.symm

/- English proof (translation)
Take `⟨⟨α, hα⟩, -, h0⟩` from `(measure fun a : {a : Fin k → ℤ // redV M a = redV M a₀} => (β (s a.1) (s a.1)).toNat).wf.has_min Set.univ ⟨⟨a₀, rfl⟩, trivial⟩`. Use `⟨α, hα, fun a ha => ?_⟩` and prove the remaining obligations. Establish `h1 : ¬ (β (s a) (s a)).toNat < (β (s α) (s α)).toNat` using `h0 ⟨a, ha⟩ trivial`. Use `h (s a)` as an intermediate fact. Use `h (s α)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem exists_classMin_attained {β : LinearMap.BilinForm ℤ X} (h : ∀ y, 0 ≤ β y y) (s : (Fin k → ℤ) →ₗ[ℤ] X)
    (a₀ : Fin k → ℤ) :
    ∃ α, redV M α = redV M a₀ ∧ ∀ a, redV M a = redV M a₀ → β (s α) (s α) ≤ β (s a) (s a) := by
  obtain ⟨⟨α, hα⟩, -, h0⟩ := (measure fun a : {a : Fin k → ℤ // redV M a = redV M a₀} =>
    (β (s a.1) (s a.1)).toNat).wf.has_min Set.univ ⟨⟨a₀, rfl⟩, trivial⟩
  refine ⟨α, hα, fun a ha => ?_⟩
  have h1 : ¬ (β (s a) (s a)).toNat < (β (s α) (s α)).toNat := h0 ⟨a, ha⟩ trivial
  have := h (s a)
  have := h (s α)
  omega

/- English proof (translation)
Take `⟨k, s, hs⟩` from `Module.Finite.exists_fin' ℤ X`. Introduce `y`. Take `⟨a₀, rfl⟩` from `hs y`. Set `σ : LinearMap.BilinForm ℤ X` to `∑ i, γ i`. Establish `hσa : ∀ a b, σ a b = ∑ i, γ i a b` using `fun a b => by simp [σ, LinearMap.sum_apply]`.

Establish `hσ : ∀ y, 0 ≤ σ y y` using `fun y => by`. Rewrite using `[hσa]`. Conclude with `Finset.sum_nonneg fun i _ => h i y`. Take `⟨α, hα, hmin⟩` from `exists_classMin_attained M hσ s a₀`. Take `⟨d, hd⟩` from `exists_eq_add_of_redV_eq hα`.

Establish `hcm` using `classMin_sum_eq M h hs he (redV M a₀)`. Establish `hval : classMin M (rd s fun a b => ∑ i, (1 : ℝ) * (γ i a b : ℝ)) (redV M a₀) = ((σ (s α) (s α) : ℤ) : ℝ)`. Use `IsLeast.csInf_eq ⟨⟨α, hα, ?_⟩, ?_⟩` and prove the remaining obligations. Simplify using `[rd, hσa]`. Introduce and unpack `x ⟨a, ha, rfl⟩`.

Use `hmin a ha` as an intermediate fact. Establish `h2 : ((σ (s α) (s α) : ℤ) : ℝ) ≤ ((σ (s a) (s a) : ℤ) : ℝ)` using `by exact_mod_cast this`. Simplify `h2` using `[rd, hσa]`. Establish `hle : ∀ i, classMin M (rd s fun a b => (γ i a b : ℝ)) (redV M a₀) ≤ (γ i (s α) (s α) : ℝ)` using `fun i => by`. Rewrite using `[← hα]`.

Conclude with `classMin_le M (h i) s α`. Establish `hsum : ∑ i, classMin M (rd s fun a b => (γ i a b : ℝ)) (redV M a₀) = ∑ i, (γ i (s α) (s α) : ℝ)`. Rewrite `hcm` using `[hval]`. Simplify using `only [one_mul] at hcm`. Rewrite using `[← hcm, hσa]`.

Use `push_cast`. Both sides reduce to the same expression. Establish `heq` using `(Finset.sum_eq_sum_iff_of_le fun i _ => hle i).1 hsum`. Use `⟨s d, fun i μ => ?_⟩` and prove the remaining obligations. Take `⟨e, rfl⟩` from `hs μ`.

Establish `hn : ∀ x : X, (M + 1) • x = ((M : ℤ) + 1) • x` using `fun x => by`. Rewrite using `[← natCast_zsmul]`. Use `push_cast`. Both sides reduce to the same expression. Establish `e1 : s a₀ + (M + 1) • s d = s α`.

Rewrite using `[hd, map_add, map_smul, hn]`. Establish `e2 : s a₀ + (M + 1) • s e = s (a₀ + ((M : ℤ) + 1) • e)`. Rewrite using `[map_add, map_smul, hn]`. Rewrite using `[e1, e2]`. Establish `h3` using `classMin_le M (h i) s (a₀ + ((M : ℤ) + 1) • e)`.

Rewrite `h3` using `[redV_add_smul, heq i (Finset.mem_univ i)]`. Conclude with `h3` after adjusting the coercions.
-/
theorem isFine_of_additive [Module.Finite ℤ X] {γ : Fin m → LinearMap.BilinForm ℤ X} (h : ∀ i y, 0 ≤ γ i y y)
    (he : (fineMean M).eval X (fun a b => ∑ i, (1 : ℝ) * (γ i a b : ℝ)) = ∑ i, (1 : ℝ) * (fineMean M).evalZ (γ i)) :
    IsFine (M + 1) γ := by
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin' ℤ X
  intro y
  obtain ⟨a₀, rfl⟩ := hs y
  let σ : LinearMap.BilinForm ℤ X := ∑ i, γ i
  have hσa : ∀ a b, σ a b = ∑ i, γ i a b := fun a b => by simp [σ, LinearMap.sum_apply]
  have hσ : ∀ y, 0 ≤ σ y y := fun y => by
    rw [hσa]; exact Finset.sum_nonneg fun i _ => h i y
  obtain ⟨α, hα, hmin⟩ := exists_classMin_attained M hσ s a₀
  obtain ⟨d, hd⟩ := exists_eq_add_of_redV_eq hα
  have hcm := classMin_sum_eq M h hs he (redV M a₀)

  have hval : classMin M (rd s fun a b => ∑ i, (1 : ℝ) * (γ i a b : ℝ)) (redV M a₀) = ((σ (s α) (s α) : ℤ) : ℝ) := by
    refine IsLeast.csInf_eq ⟨⟨α, hα, ?_⟩, ?_⟩
    · simp [rd, hσa]
    · rintro x ⟨a, ha, rfl⟩
      have := hmin a ha
      have h2 : ((σ (s α) (s α) : ℤ) : ℝ) ≤ ((σ (s a) (s a) : ℤ) : ℝ) := by exact_mod_cast this
      simpa [rd, hσa] using h2
  have hle : ∀ i, classMin M (rd s fun a b => (γ i a b : ℝ)) (redV M a₀) ≤ (γ i (s α) (s α) : ℝ) := fun i => by
    rw [← hα]; exact classMin_le M (h i) s α
  have hsum : ∑ i, classMin M (rd s fun a b => (γ i a b : ℝ)) (redV M a₀) = ∑ i, (γ i (s α) (s α) : ℝ) := by
    rw [hval] at hcm
    simp only [one_mul] at hcm
    rw [← hcm, hσa]
    push_cast
    rfl
  have heq := (Finset.sum_eq_sum_iff_of_le fun i _ => hle i).1 hsum
  refine ⟨s d, fun i μ => ?_⟩
  obtain ⟨e, rfl⟩ := hs μ
  have hn : ∀ x : X, (M + 1) • x = ((M : ℤ) + 1) • x := fun x => by
    rw [← natCast_zsmul]; push_cast; rfl
  have e1 : s a₀ + (M + 1) • s d = s α := by
    rw [hd, map_add, map_smul, hn]
  have e2 : s a₀ + (M + 1) • s e = s (a₀ + ((M : ℤ) + 1) • e) := by
    rw [map_add, map_smul, hn]
  rw [e1, e2]
  have h3 := classMin_le M (h i) s (a₀ + ((M : ℤ) + 1) • e)
  rw [redV_add_smul, heq i (Finset.mem_univ i)] at h3
  exact_mod_cast h3

end Mean

end GlobalTheory.PolFan.LinOn

open GlobalTheory.PolFan.LinOn in

/- English proof (translation)
Use `haveI : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X`. Use `haveI : Module.Projective ℤ X := by`. Take `⟨n, r, hr⟩` from `Module.Finite.exists_fin' (𝓞 E) X`. Take `⟨h, hh⟩` from `Module.projective_lifting_property r LinearMap.id hr`. Conclude with `Module.Projective.of_split (h.restrictScalars ℤ) (r.restrictScalars ℤ) (LinearMap.ext fun x => LinearMap.congr_fun hh x)`.

Establish `hrank : Module.finrank ℤ X ≤ g`. Rewrite using `[finrank_int_eq' E X]`. Conclude with `(Nat.mul_le_mul_left _ hX).trans hq`. Establish `hpol : IsPolFanOn (id : ℤ → ℤ) φs X` using `hφ X hrank`. Establish `h1 : ∀ i, γ i ∈ balForms (id : ℤ → ℤ) X` using `fun i => mem_balForms_int.2 (hb i).1`.

Establish `hDr : (0 : ℝ) < D` using `by exact_mod_cast hD`. Establish `hsplit : ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → φs.eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) = ∑ i, c i * φs.evalZ (γ i) ∧ ∀ M ∈ 𝓜, (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) = ∑ i, c i * (fineMean M).evalZ (γ i)`. Introduce `c hc`. Establish `e0 : ∑ i, c i * φs.evalZ (γ i) ≤ φs.eval X (fun a b => ∑ i, c i * (γ i a b : ℝ))`. Use `sum_le_evalR hpol h1 hp hc` as an intermediate fact.

Simplify `this` using `[evalR, LinearMap.sum_apply]`. Establish `eM : ∀ M ∈ 𝓜, ∑ i, c i * (fineMean M).evalZ (γ i) ≤ (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ))` using `fun M _ => sum_fineMean_le M hp hc`. Establish `e3 : φs.eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) + ∑ M ∈ 𝓜, (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) = ∑ i, c i * φs.evalZ (γ i) + ∑ M ∈ 𝓜, ∑ i, c i * (fineMean M).evalZ (γ i)`. Establish `e4 : ∑ i, c i * ((D : ℝ) * (φs.evalZ (γ i) + ∑ M ∈ 𝓜, (fineMean M).evalZ (γ i))) = D * (∑ i, c i * φs.evalZ (γ i) + ∑ M ∈ 𝓜, ∑ i, c i * (fineMean M).evalZ (γ i))`. Establish `e7 : ∀ i, c i * ((D : ℝ) * (φs.evalZ (γ i) + ∑ M ∈ 𝓜, (fineMean M).evalZ (γ i))) = D * (c i * φs.evalZ (γ i) + ∑ M ∈ 𝓜, c i * (fineMean M).evalZ (γ i))` using `fun i => by`.

Rewrite using `[← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e7]`. Rewrite using `[← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm (s := Finset.univ)]`. Establish `h2 : (D : ℝ) * (φs.eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) + ∑ M ∈ 𝓜, (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ))) = ∑ i, c i * ((D : ℝ) * (φs.evalZ (γ i) + ∑ M ∈ 𝓜, (fineMean M).evalZ (γ i)))`.

Simplify `hl c hc` using `only [InvFun.evalZ, eval_baseFun]`. Rewrite `h2` using `[e4]`. Conclude with `mul_left_cancel₀ hDr.ne' h2`. Establish `hs2 : ∑ M ∈ 𝓜, ∑ i, c i * (fineMean M).evalZ (γ i) ≤ ∑ M ∈ 𝓜, (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ))` using `Finset.sum_le_sum eM`. Establish `e5 : φs.eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) = ∑ i, c i * φs.evalZ (γ i)` using `by linarith`.

Use `⟨e5, ?_⟩` and prove the remaining obligations. Establish `e6 : ∑ M ∈ 𝓜, ∑ i, c i * (fineMean M).evalZ (γ i) = ∑ M ∈ 𝓜, (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ))` using `by linarith`. Conclude with `fun M hM => ((Finset.sum_eq_sum_iff_of_le eM).1 e6 M hM).symm`. Use `⟨fun c hc => ?_, fun M hM => ?_⟩` and prove the remaining obligations. Simplify using `only [InvFun.evalZ, eval_restr]`.

Conclude with `(hsplit c hc).1`. Conclude with `isFine_of_additive M hp ((hsplit (fun _ => 1) fun _ => zero_le_one).2 M hM)`.
-/
theorem GlobalTheory.PolFan.linearOn_and_isFine_of_linearOn_baseFun (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (g q D : ℕ) (φs : InvFun ℤ) (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X]
    [Module.Projective (𝓞 E) X] (hD : 0 < D) (hφ : IsPolFan (id : ℤ → ℤ) g φs) (hq : Module.finrank ℚ E * q ≤ g)
    (hX : Module.finrank (𝓞 E) X ≤ q) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (hb : ∀ i, γ i ∈ balForms H.bar X)
    (hp : ∀ i y, 0 ≤ γ i y y) (hl : (baseFun (𝓞 E) D φs 𝓜).LinearOn γ) :
    (restr (𝓞 E) φs).LinearOn γ ∧ ∀ M ∈ 𝓜, IsFine (M + 1) γ := by
  haveI : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  haveI : Module.Projective ℤ X := by
    obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' (𝓞 E) X
    obtain ⟨h, hh⟩ := Module.projective_lifting_property r LinearMap.id hr
    exact Module.Projective.of_split (h.restrictScalars ℤ) (r.restrictScalars ℤ)
      (LinearMap.ext fun x => LinearMap.congr_fun hh x)
  have hrank : Module.finrank ℤ X ≤ g := by
    rw [finrank_int_eq' E X]
    exact (Nat.mul_le_mul_left _ hX).trans hq
  have hpol : IsPolFanOn (id : ℤ → ℤ) φs X := hφ X hrank
  have h1 : ∀ i, γ i ∈ balForms (id : ℤ → ℤ) X := fun i => mem_balForms_int.2 (hb i).1
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD

  have hsplit : ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) →
      φs.eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) = ∑ i, c i * φs.evalZ (γ i) ∧
      ∀ M ∈ 𝓜, (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) = ∑ i, c i * (fineMean M).evalZ (γ i) := by
    intro c hc
    have e0 : ∑ i, c i * φs.evalZ (γ i) ≤ φs.eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) := by
      have := sum_le_evalR hpol h1 hp hc
      simpa [evalR, LinearMap.sum_apply] using this
    have eM : ∀ M ∈ 𝓜, ∑ i, c i * (fineMean M).evalZ (γ i) ≤
        (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) := fun M _ => sum_fineMean_le M hp hc
    have e3 : φs.eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) +
        ∑ M ∈ 𝓜, (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) =
        ∑ i, c i * φs.evalZ (γ i) + ∑ M ∈ 𝓜, ∑ i, c i * (fineMean M).evalZ (γ i) := by
      have e4 : ∑ i, c i * ((D : ℝ) * (φs.evalZ (γ i) + ∑ M ∈ 𝓜, (fineMean M).evalZ (γ i))) =
          D * (∑ i, c i * φs.evalZ (γ i) + ∑ M ∈ 𝓜, ∑ i, c i * (fineMean M).evalZ (γ i)) := by
        have e7 : ∀ i, c i * ((D : ℝ) * (φs.evalZ (γ i) + ∑ M ∈ 𝓜, (fineMean M).evalZ (γ i))) =
            D * (c i * φs.evalZ (γ i) + ∑ M ∈ 𝓜, c i * (fineMean M).evalZ (γ i)) := fun i => by
          rw [← Finset.mul_sum]; ring
        simp only [e7]
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm (s := Finset.univ)]
      have h2 : (D : ℝ) * (φs.eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) +
          ∑ M ∈ 𝓜, (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ))) =
          ∑ i, c i * ((D : ℝ) * (φs.evalZ (γ i) + ∑ M ∈ 𝓜, (fineMean M).evalZ (γ i))) := by
        simpa only [InvFun.evalZ, eval_baseFun] using hl c hc
      rw [e4] at h2
      exact mul_left_cancel₀ hDr.ne' h2
    have hs2 : ∑ M ∈ 𝓜, ∑ i, c i * (fineMean M).evalZ (γ i) ≤
        ∑ M ∈ 𝓜, (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) := Finset.sum_le_sum eM
    have e5 : φs.eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) = ∑ i, c i * φs.evalZ (γ i) := by linarith
    refine ⟨e5, ?_⟩
    have e6 : ∑ M ∈ 𝓜, ∑ i, c i * (fineMean M).evalZ (γ i) =
        ∑ M ∈ 𝓜, (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) := by linarith
    exact fun M hM => ((Finset.sum_eq_sum_iff_of_le eM).1 e6 M hM).symm
  refine ⟨fun c hc => ?_, fun M hM => ?_⟩
  · simp only [InvFun.evalZ, eval_restr]
    exact (hsplit c hc).1
  · exact isFine_of_additive M hp ((hsplit (fun _ => 1) fun _ => zero_le_one).2 M hM)
