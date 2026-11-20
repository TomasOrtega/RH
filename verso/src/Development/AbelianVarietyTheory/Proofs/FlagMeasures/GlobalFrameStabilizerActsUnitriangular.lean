import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section
namespace GlobalTheory.HL.StTri

/- English proof (translation)
Use `letI : Algebra E R := ι.toAlgebra`. Establish `hinj : Function.Injective (Algebra.linearMap E R)` using `ι.injective`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (Algebra.linearMap E R) (LinearMap.ker_eq_bot.mpr hinj)`. Establish `hg1 : ∀ c : E, g (ι c) = c` using `fun c => LinearMap.congr_fun hg c`. Establish `hgm : ∀ (a : R) (c : E), g (a * ι c) = c * g a`.

Introduce `a c`. Establish `: a * ι c = c • a` using `by rw [Algebra.smul_def, mul_comm]; rfl`. Rewrite using `[this, map_smul, smul_eq_mul]`. Rewrite `h` using `[Finsupp.mem_span_image_iff_linearCombination]`. Take `⟨l, hl, hv⟩` from `h`.

Rewrite using `[Finsupp.mem_span_image_iff_linearCombination]`. Use `⟨Finsupp.mapRange g (map_zero g) l, ?_, ?_⟩` and prove the remaining obligations. Rewrite `hl`, the goal using `[Finsupp.mem_supported']`. Introduce `i hi`. Simplify using `[hl i hi]`.

Use function extensionality and compare the values at `k`. Establish `hk` using `congrFun hv k`. Rewrite `hk`, the goal using `[Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hk ⊢`. Rewrite using `[← hg1 (v k), ← hk, map_sum]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[hgm, Finsupp.mapRange_apply, mul_comm]`.
-/
theorem descend {E R : Type} [Field E] [CommRing R] [Nontrivial R] (ι : E →+* R) {n m : ℕ}
    (w : Fin m → Fin n → E) (s : Set (Fin m)) (v : Fin n → E)
    (h : (fun i => ι (v i)) ∈ Submodule.span R ((fun a i => ι (w a i)) '' s)) :
    v ∈ Submodule.span E (w '' s) := by
  letI : Algebra E R := ι.toAlgebra
  have hinj : Function.Injective (Algebra.linearMap E R) := ι.injective
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap E R)
    (LinearMap.ker_eq_bot.mpr hinj)
  have hg1 : ∀ c : E, g (ι c) = c := fun c => LinearMap.congr_fun hg c
  have hgm : ∀ (a : R) (c : E), g (a * ι c) = c * g a := by
    intro a c
    have : a * ι c = c • a := by rw [Algebra.smul_def, mul_comm]; rfl
    rw [this, map_smul, smul_eq_mul]
  rw [Finsupp.mem_span_image_iff_linearCombination] at h
  obtain ⟨l, hl, hv⟩ := h
  rw [Finsupp.mem_span_image_iff_linearCombination]
  refine ⟨Finsupp.mapRange g (map_zero g) l, ?_, ?_⟩
  · rw [Finsupp.mem_supported'] at hl ⊢
    intro i hi
    simp [hl i hi]
  · funext k
    have hk := congrFun hv k
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hk ⊢
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hk ⊢
    rw [← hg1 (v k), ← hk, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hgm, Finsupp.mapRange_apply, mul_comm]

/- English proof (translation)
Simplify using `only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_smul_right {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (c : E) :
    hf L Hm x (c • y) = L.cj c * hf L Hm x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `only [hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]`.
-/
theorem hf_add_right {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x y z : Fin n → E) :
    hf L Hm x (y + z) = hf L Hm x y + hf L Hm x z := by
  simp only [hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Unfold `Frames.Nof at hx`. Rewrite `hx` using `[Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_iInf]`. Take `⟨⟨_, hU⟩, hP⟩` from `hx`. Distinguish the cases in `hj : (j : ℕ) < r`. Establish `h1` using `(hU ⟨j, hj⟩).2 (g j) (Submodule.subset_span ⟨j, by simp, rfl⟩)`.

Simplify using `using h1`. Establish `hjr : (j : ℕ) = r` using `by omega`. Establish `hjl : j = Fin.last r` using `Fin.ext hjr`. Establish `hmem : g (Fin.last r) ∈ perp L S.Hm (S.spanTo g r)`. Introduce `y hy`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨b, hb, rfl⟩` from `hy`. Conclude with `hg b hb`. Consider the case `zero => simp [hf]`.

Consider the case `add y z _ _ hy hz => rw [hf_add_right, hy, hz, add_zero]`. Consider the case `smul c y _ hy => rw [hf_smul_right, hy, mul_zero]`. Establish `h2` using `hP.2 _ hmem`. Rewrite using `[hjl]`. Simplify `h2` using `[Frames.spanTo]`.
-/
theorem loc_step {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V)
    (hg : ∀ b : Fin (r + 1), (b : ℕ) < r → hf L S.Hm (g (Fin.last r)) (g b) = 0)
    (x : S.GLV) (hx : x ∈ S.Nof g) (j : Fin (r + 1)) : x (g j) - g j ∈ S.spanTo g j := by
  unfold Frames.Nof at hx
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_iInf] at hx
  obtain ⟨⟨_, hU⟩, hP⟩ := hx
  by_cases hj : (j : ℕ) < r
  · have h1 := (hU ⟨j, hj⟩).2 (g j) (Submodule.subset_span ⟨j, by simp, rfl⟩)
    simpa using h1
  · have hjr : (j : ℕ) = r := by omega
    have hjl : j = Fin.last r := Fin.ext hjr
    have hmem : g (Fin.last r) ∈ perp L S.Hm (S.spanTo g r) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨b, hb, rfl⟩ := hy
        exact hg b hb
      | zero => simp [hf]
      | add y z _ _ hy hz => rw [hf_add_right, hy, hz, add_zero]
      | smul c y _ hy => rw [hf_smul_right, hy, mul_zero]
    have h2 := hP.2 _ hmem
    rw [hjl]
    simpa [Frames.spanTo] using h2

/- English proof (translation)
Use `haveI : Nontrivial (A.loc p).Ep := Module.nontrivial_of_finrank_pos (R := (A.loc p).Fp) (by rw [(A.loc p).rank]; norm_num)`. Establish `key : ∀ j : Fin (r + 1), x (gG j) - gG j ∈ Submodule.span E (gG '' {i | (i : ℕ) < j})`. Introduce `j`. Apply `descend (A.loc p).ιE gG` to reduce the goal to its premises. Establish `e1 : (fun i => (A.loc p).ιE ((x (gG j) - gG j) i)) = u j • (xp (gS j) - gS j)`.

Rewrite using `[smul_sub, ← map_smul, heq, hext]`. Use function extensionality and compare the values at `i`. Simplify using `[Places.bc]`. Rewrite using `[e1]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations.

Use `(Submodule.span_le.mpr ?_) (hstep j)` and prove the remaining obligations. Introduce and unpack `_ ⟨i, hi, rfl⟩`. Establish `h3 : gS i = ((hu i).unit⁻¹ : ((A.loc p).Ep)ˣ) • A.bc p (gG i)`. Rewrite using `[← heq, Units.smul_def, smul_smul, (hu i).val_inv_mul, one_smul]`. Rewrite using `[h3]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)`. Establish `key2 : ∀ j : Fin (r + 1), ∃ l : Fin (r + 1) →₀ E, l ∈ Finsupp.supported E E {i : Fin (r + 1) | (i : ℕ) < j} ∧ Finsupp.linearCombination E gG l = x (gG j) - gG j` using `fun j => (Finsupp.mem_span_image_iff_linearCombination E).mp (key j)`. Use `choose l hl hl' using key2`. Establish `hz : ∀ i j : Fin (r + 1), ¬ ((i : ℕ) < j) → l j i = 0` using `fun i j h => (Finsupp.mem_supported' _ _).mp (hl j) i h`. Use `⟨Matrix.of fun i j => if i = j then 1 else l j i, ⟨fun i j hij => ?_, fun i => ?_⟩, fun j => ?_⟩` and prove the remaining obligations.

Establish `hne : i ≠ j` using `fun h => by subst h; exact lt_irrefl _ hij`. Simplify using `only [Matrix.of_apply, if_neg hne]`. Conclude with `hz i j (by rw [Fin.lt_def] at hij; omega)`. Simplify using the standard rewrite rules. Establish `hjj : l j j = 0` using `hz j j (lt_irrefl _)`.

Establish `hsplit : ∀ i, (if i = j then (1 : E) else l j i) = (if i = j then 1 else 0) + l j i`. Introduce `i`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[hjj]`.

Simplify using `[h]`. Establish `hlc` using `hl' j`. Rewrite `hlc` using `[Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]`. Simplify using `only [Matrix.of_apply, hsplit, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, hlc]`. Normalize the expressions using the abelian group laws.
-/
theorem frame_tri {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) {r n : ℕ} (p : HeightOneSpectrum (𝓞 F))
    (x : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (xp : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)) (hext : A.Ext p x xp)
    (gG : Fin (r + 1) → Fin n → E) (gS : Fin (r + 1) → Fin n → (A.loc p).Ep)
    (u : Fin (r + 1) → (A.loc p).Ep) (hu : ∀ a, IsUnit (u a)) (heq : ∀ a, u a • gS a = A.bc p (gG a))
    (hstep : ∀ j : Fin (r + 1), xp (gS j) - gS j ∈ Submodule.span (A.loc p).Ep (gS '' {i | (i : ℕ) < j})) :
    ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧
      ∀ j, x (gG j) = ∑ i, s i j • gG i := by
  haveI : Nontrivial (A.loc p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (A.loc p).Fp) (by rw [(A.loc p).rank]; norm_num)
  have key : ∀ j : Fin (r + 1), x (gG j) - gG j ∈ Submodule.span E (gG '' {i | (i : ℕ) < j}) := by
    intro j
    apply descend (A.loc p).ιE gG
    have e1 : (fun i => (A.loc p).ιE ((x (gG j) - gG j) i)) = u j • (xp (gS j) - gS j) := by
      rw [smul_sub, ← map_smul, heq, hext]
      funext i
      simp [Places.bc]
    rw [e1]
    refine Submodule.smul_mem _ _ ?_
    refine (Submodule.span_le.mpr ?_) (hstep j)
    rintro _ ⟨i, hi, rfl⟩
    have h3 : gS i = ((hu i).unit⁻¹ : ((A.loc p).Ep)ˣ) • A.bc p (gG i) := by
      rw [← heq, Units.smul_def, smul_smul, (hu i).val_inv_mul, one_smul]
    rw [h3]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  have key2 : ∀ j : Fin (r + 1), ∃ l : Fin (r + 1) →₀ E,
      l ∈ Finsupp.supported E E {i : Fin (r + 1) | (i : ℕ) < j} ∧
      Finsupp.linearCombination E gG l = x (gG j) - gG j := fun j =>
    (Finsupp.mem_span_image_iff_linearCombination E).mp (key j)
  choose l hl hl' using key2
  have hz : ∀ i j : Fin (r + 1), ¬ ((i : ℕ) < j) → l j i = 0 := fun i j h =>
    (Finsupp.mem_supported' _ _).mp (hl j) i h
  refine ⟨Matrix.of fun i j => if i = j then 1 else l j i, ⟨fun i j hij => ?_, fun i => ?_⟩, fun j => ?_⟩
  · have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
    simp only [Matrix.of_apply, if_neg hne]
    exact hz i j (by rw [Fin.lt_def] at hij; omega)
  · simp
  · have hjj : l j j = 0 := hz j j (lt_irrefl _)
    have hsplit : ∀ i, (if i = j then (1 : E) else l j i) = (if i = j then 1 else 0) + l j i := by
      intro i
      by_cases h : i = j
      · subst h; simp [hjj]
      · simp [h]
    have hlc := hl' j
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hlc
    simp only [Matrix.of_apply, hsplit, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, hlc]
    abel

/- English proof (translation)
Introduce `F E _ _ _ _ _ sig A r k G x hx`. Choose the witnesses or unpack the hypotheses as in `⟨p⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := by`. Take `⟨M, hM⟩` from `Ideal.exists_maximal (𝓞 F)`. Conclude with `⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩⟩`. Take `⟨xp, hxp, hext⟩` from `(show ∀ p, ∃ g' ∈ (G.S p).St, A.Ext p x g' from hx) p`.

Establish `hxp'` using `Subgroup.mem_inf.mp hxp`. Establish `hunit : ∀ a : Fin (r + 1), IsUnit (algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (a : ℕ))))` using `fun a => ((G.c p).isUnit.pow _).map _`. Take `⟨s, hs, hsx⟩` from `frame_tri A p x xp hext G.f (G.S p).f _ hunit (G.f_eq p) (loc_step (G.S p) (G.S p).f (fun b hb => by`. Rewrite using `[(G.S p).gram]`. Establish `: b ≠ Fin.last r` using `fun h => by subst h; simp at hb`.

Simplify using `[this]) xp hxp'.1)`. Take `⟨s', hs', hsx'⟩` from `frame_tri A p x xp hext G.f' (G.S p).f' _ hunit (G.f'_eq p) (loc_step (G.S p) (G.S p).f' (fun b hb => by`. Rewrite using `[(G.S p).gram']`. Establish `: b ≠ Fin.last r` using `fun h => by subst h; simp at hb`. Simplify using `[this]) xp hxp'.2)`.

Conclude with `⟨s, s', hs, hs', hsx, hsx'⟩`.
-/
theorem stab_unitriangular : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ x ∈ G.St, ∃ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧ ((∀ i j, j < i → s' i j = 0) ∧ (∀ i, s' i i = 1)) ∧ (∀ j, x (G.f j) = ∑ i, s i j • G.f i) ∧ ∀ j, x (G.f' j) = ∑ i, s' i j • G.f' i := by
  intro F E _ _ _ _ _ sig A r k G x hx
  obtain ⟨p⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩⟩
  obtain ⟨xp, hxp, hext⟩ := (show ∀ p, ∃ g' ∈ (G.S p).St, A.Ext p x g' from hx) p
  have hxp' := Subgroup.mem_inf.mp hxp
  have hunit : ∀ a : Fin (r + 1), IsUnit (algebraMap (A.loc p).Fp (A.loc p).Ep
      (((G.c p : (A.loc p).Fp)) ^ (r - (a : ℕ)))) := fun a =>
    ((G.c p).isUnit.pow _).map _
  obtain ⟨s, hs, hsx⟩ := frame_tri A p x xp hext G.f (G.S p).f _ hunit (G.f_eq p)
    (loc_step (G.S p) (G.S p).f (fun b hb => by
      rw [(G.S p).gram]
      have : b ≠ Fin.last r := fun h => by subst h; simp at hb
      simp [this]) xp hxp'.1)
  obtain ⟨s', hs', hsx'⟩ := frame_tri A p x xp hext G.f' (G.S p).f' _ hunit (G.f'_eq p)
    (loc_step (G.S p) (G.S p).f' (fun b hb => by
      rw [(G.S p).gram']
      have : b ≠ Fin.last r := fun h => by subst h; simp at hb
      simp [this]) xp hxp'.2)
  exact ⟨s, s', hs, hs', hsx, hsx'⟩

end GlobalTheory.HL.StTri
