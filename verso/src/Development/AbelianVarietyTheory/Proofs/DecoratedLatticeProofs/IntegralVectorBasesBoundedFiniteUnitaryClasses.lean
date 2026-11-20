import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralMatrixRelatingIntegralVectorZBasesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryOfPreservesHermitianTraceFormIntegralBasiStatement
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

namespace GlobalTheory.BasesFin

/- English proof (translation)
Introduce `I`. Take `⟨y, hy0, hyi⟩` from `exists_integral_multiples ℤ ℚ (Finset.univ.image fun p : Fin I.n × Fin I.n => I.J p.1 p.2)`. Use `⟨y.natAbs, Int.natAbs_pos.mpr hy0, ?_⟩` and prove the remaining obligations. Establish `hcJ : ∀ a b, IsIntegral ℤ ((y.natAbs : I.E) * I.J a b)`. Introduce `a b`.

Establish `h` using `hyi (I.J a b) (Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, rfl⟩)`. Rewrite `h` using `[zsmul_eq_mul]`. Break down `Int.natAbs_eq y with hy | hy` into its components or cases. Rewrite `h` using `[hy]`. Simplify using `using h`.

Rewrite `h` using `[hy]`. Use `h.neg` as an intermediate fact. Simplify `this` using `[neg_mul]`. Introduce `x z hx hz`. Establish `hint : IsIntegral ℤ ((y.natAbs : I.E) * Formalism.UG.hform (starRingEnd I.E) I.J x z)`.

Unfold `Formalism.UG.hform`. Rewrite using `[Finset.mul_sum]`. Use `IsIntegral.sum _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `IsIntegral.sum _ fun j _ => ?_` and prove the remaining obligations.

Establish `: (y.natAbs : I.E) * ((starRingEnd I.E) (x i) * I.J i j * z j) = (starRingEnd I.E) (x i) * ((y.natAbs : I.E) * I.J i j) * z j` using `by ring`. Rewrite using `[this]`. Establish `hs : IsIntegral ℤ ((starRingEnd I.E) (x i))` using `(hx i).map (starRingEnd I.E).toIntAlgHom`. Conclude with `(hs.mul (hcJ i j)).mul (hz j)`. Establish `htr` using `Algebra.isIntegral_trace (R := ℤ) (L := ℚ) hint`.

Take `⟨m, hm⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp htr`. Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite `hm` using `[eq_intCast]`. Rewrite using `[hm]`. Unfold `trForm`.

Rewrite using `[← map_natCast (algebraMap ℚ I.E), ← Algebra.smul_def, map_smul, smul_eq_mul]`.
-/
theorem trForm_denom : ∀ (I : AutInst), ∃ c : ℕ, 0 < c ∧ ∀ x y : Fin I.n → I.E, IntVec I x → IntVec I y →
    ∃ m : ℤ, (c : ℚ) * trForm I x y = m := by
  intro I
  classical
  obtain ⟨y, hy0, hyi⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image fun p : Fin I.n × Fin I.n => I.J p.1 p.2)
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ?_⟩
  have hcJ : ∀ a b, IsIntegral ℤ ((y.natAbs : I.E) * I.J a b) := by
    intro a b
    have h := hyi (I.J a b) (Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, rfl⟩)
    rw [zsmul_eq_mul] at h
    rcases Int.natAbs_eq y with hy | hy
    · rw [hy] at h; simpa using h
    · rw [hy] at h
      have := h.neg
      simpa [neg_mul] using this
  intro x z hx hz
  have hint : IsIntegral ℤ ((y.natAbs : I.E) * Formalism.UG.hform (starRingEnd I.E) I.J x z) := by
    unfold Formalism.UG.hform
    rw [Finset.mul_sum]
    refine IsIntegral.sum _ fun i _ => ?_
    rw [Finset.mul_sum]
    refine IsIntegral.sum _ fun j _ => ?_
    have : (y.natAbs : I.E) * ((starRingEnd I.E) (x i) * I.J i j * z j)
        = (starRingEnd I.E) (x i) * ((y.natAbs : I.E) * I.J i j) * z j := by ring
    rw [this]
    have hs : IsIntegral ℤ ((starRingEnd I.E) (x i)) := (hx i).map (starRingEnd I.E).toIntAlgHom
    exact (hs.mul (hcJ i j)).mul (hz j)
  have htr := Algebra.isIntegral_trace (R := ℤ) (L := ℚ) hint
  obtain ⟨m, hm⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp htr
  refine ⟨m, ?_⟩
  rw [eq_intCast] at hm
  rw [hm]
  unfold trForm
  rw [← map_natCast (algebraMap ℚ I.E), ← Algebra.smul_def, map_smul, smul_eq_mul]

/- English proof (translation)
Establish `key : ∀ u, IntVec I u → A *ᵥ u = u`. Introduce `u hu`. Take `⟨z, rfl⟩` from `(he.2 u).1 hu`. Rewrite using `[Matrix.mulVec_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mulVec_smul, hA]`. Use extensionality with `i j`. Establish `hs : IntVec I (Pi.single j 1)`. Introduce `l`. Distinguish the cases in `h : l = j`.

Substitute `h` using the available equality. Simplify using `using isIntegral_one`. Simplify using `[Pi.single_apply, h, isIntegral_zero]`. Use `congrFun (key _ hs) i` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_single_one]`.

Simplify `this` using `[Matrix.col, Matrix.one_apply, Pi.single_apply, eq_comm]`.
-/
theorem fix_one (I : AutInst) {N : ℕ} (e : Fin N → Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I.n) I.E)
    (he : IsZBasis I e) (hA : ∀ j, A *ᵥ e j = e j) : A = 1 := by
  have key : ∀ u, IntVec I u → A *ᵥ u = u := by
    intro u hu
    obtain ⟨z, rfl⟩ := (he.2 u).1 hu
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, hA]
  ext i j
  have hs : IntVec I (Pi.single j 1) := by
    intro l
    by_cases h : l = j
    · subst h; simpa using isIntegral_one
    · simp [Pi.single_apply, h, isIntegral_zero]
  have := congrFun (key _ hs) i
  rw [Matrix.mulVec_single_one] at this
  simpa [Matrix.col, Matrix.one_apply, Pi.single_apply, eq_comm] using this

/- English proof (translation)
Introduce `I N R`. Take `⟨c, hc0, hc⟩` from `trForm_denom I`. Set `T` to `(Module.Free.ChooseBasisIndex ℤ (𝓞 I.E) → Fin N → Fin N → ℤ) × (Fin N → Fin N → ℚ)`. Set `has : (Fin N → Fin I.n → I.E) → T → Prop` to `fun e t => (∀ k j, (integralBasis I.E k : I.E) • e j = ∑ i, t.1 k j i • e i) ∧ ∀ i j, trForm I (e i) (e j) = t.2 i j`. Set `A : Set T` to `(Set.univ.pi fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => {z : ℤ | |(z:ℝ)| ≤ R}) ×ˢ (Set.univ.pi fun _ => Set.univ.pi fun _ => {q : ℚ | |(q:ℝ)| ≤ R ∧ ∃ m : ℤ, (c:ℚ) * q = m})`.

Establish `hZ : {z : ℤ | |(z:ℝ)| ≤ R}.Finite`. Use `(Set.finite_Icc (-⌈R⌉) ⌈R⌉).subset fun z hz => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hz`. Establish `h` using `abs_le.mp hz`. Establish `hR` using `Int.le_ceil R`.

Prove the components needed by the constructor for the conclusion. Establish `: (-(⌈R⌉:ℝ)) ≤ z` using `by linarith`. Conclude with `this` after adjusting the coercions. Establish `: (z:ℝ) ≤ ⌈R⌉` using `by linarith`. Conclude with `this` after adjusting the coercions.

Establish `hQ : {q : ℚ | |(q:ℝ)| ≤ R ∧ ∃ m : ℤ, (c:ℚ) * q = m}.Finite`. Use `((Set.finite_Icc (-⌈R * c⌉) ⌈R * c⌉).image fun m : ℤ => (m : ℚ) / c).subset ?_` and prove the remaining obligations. Introduce and unpack `q ⟨hq, m, hm⟩`. Establish `hcpos : (0:ℝ) < c` using `by exact_mod_cast hc0`. Establish `hmq : (m:ℝ) = c * q` using `by exact_mod_cast hm.symm`.

Establish `h` using `abs_le.mp hq`. Establish `hR` using `Int.le_ceil (R * c)`. Use `⟨m, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `: (-(⌈R*c⌉:ℝ)) ≤ m` using `by rw [hmq]; nlinarith`. Conclude with `this` after adjusting the coercions.

Establish `: (m:ℝ) ≤ ⌈R*c⌉` using `by rw [hmq]; nlinarith`. Conclude with `this` after adjusting the coercions. Establish `hc' : (c:ℚ) ≠ 0` using `by exact_mod_cast hc0.ne'`. Simplify using `only`. Rewrite using `[← hm]`.

Clear the denominators using the available nonvanishing facts. Establish `hA : A.Finite` using `(Set.Finite.pi fun _ => Set.Finite.pi fun _ => Set.Finite.pi fun _ => hZ).prod (Set.Finite.pi fun _ => Set.Finite.pi fun _ => hQ)`. Set `pick : T → (Fin N → Fin I.n → I.E)` to `fun t => if h : ∃ e, IsZBasis I e ∧ has e t then Classical.choose h else 0`. Establish `hpick : ∀ t (h : ∃ e, IsZBasis I e ∧ has e t), IsZBasis I (pick t) ∧ has (pick t) t`. Introduce `t h`.

Simplify using `only [pick, dif_pos h]`. Conclude with `Classical.choose_spec h`. Establish `uniq : ∀ (f : Fin N → Fin I.n → I.E) (t : T), IsZBasis I f → has f t → ∀ k j (w : Fin N → ℤ), (integralBasis I.E k : I.E) • f j = ∑ i, w i • f i → w = t.1 k j`. Introduce `f t hf hft k j w hw`. Rewrite `hw` using `[hft.1 k j]`.

Establish `h0 : ∑ i, (w i - t.1 k j i) • f i = 0`. Simplify using `only [sub_smul, Finset.sum_sub_distrib, ← hw, sub_self]`. Use function extensionality and compare the values at `i`. Conclude with `sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hf.1 _ h0 i)`. Establish `compat : ∀ (f g : Fin N → Fin I.n → I.E) (t : T), IsZBasis I f → has f t → has g t → ∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 I.E)) (j : Fin N) (w : Fin N → ℤ), (integralBasis I.E k : I.E) • f j = ∑ i, w i • f i → (integralBasis I.E k : I.E) • g j = ∑ i, w i • g i`.

Introduce `f g t hf hft hgt k j w hw`. Rewrite using `[uniq f t hf hft k j w hw]`. Conclude with `hgt.1 k j`. Use `⟨pick '' {t ∈ A | ∃ e, IsZBasis I e ∧ has e t}, (hA.subset (Set.sep_subset _ _)).image _, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨t, ⟨-, h⟩, rfl⟩`.

Conclude with `(hpick t h).1`. Introduce `e he hb choose z hz hzb using hb.1`. Set `t : T` to `(z, fun i j => trForm I (e i) (e j))`. Establish `ht : has e t` using `⟨hz, fun i j => rfl⟩`. Establish `hint : ∀ i, IntVec I (e i)` using `fun i => (he.2 (e i)).2 ⟨Pi.single i 1, by simp [Pi.single_apply]⟩`.

Establish `htA : t ∈ A` using `⟨fun k _ j _ i _ => hzb k j i, fun i _ j _ => ⟨hb.2 i j, hc _ _ (hint i) (hint j)⟩⟩`. Establish `hex : ∃ e', IsZBasis I e' ∧ has e' t` using `⟨e, he, ht⟩`. Take `⟨he₀, ht₀⟩` from `hpick t hex`. Take `⟨M, hMi, hMe⟩` from `GlobalTheory.T.exists_integralMatrix_relating_integralVectorZBases I e (pick t) he he₀ (compat e (pick t) t he ht ht₀)`. Take `⟨M', hM'i, hM'e⟩` from `GlobalTheory.T.exists_integralMatrix_relating_integralVectorZBases I (pick t) e he₀ he (compat (pick t) e t he₀ ht₀ ht)`.

Establish `h1 : M' * M = 1` using `fix_one I e _ he fun j => by rw [← Matrix.mulVec_mulVec, hMe, hM'e]`. Establish `h2 : M * M' = 1` using `(mul_eq_one_comm_of_card_eq (Fin I.n) (Fin I.n) I.E rfl).mp h1`. Set `γ : GL (Fin I.n) I.E` to `⟨M, M', h2, h1⟩`. Use `⟨pick t, ⟨t, ⟨htA, hex⟩, rfl⟩, γ, ?_, hMi, hM'i, hMe⟩` and prove the remaining obligations. Use `show Formalism.UG.cT (starRingEnd I.E) M * I.J * M = I.J`.

Conclude with `GlobalTheory.T.unitary_of_preserves_hermitianTraceForm_integralBasis I e M he fun i j => by rw [hMe, hMe]; exact ht₀.2 i j`.
-/
theorem bases_finite_classes : ∀ (I : AutInst) (N : ℕ) (R : ℝ), ∃ S : Set (Fin N → Fin I.n → I.E), S.Finite ∧ (∀ e₀ ∈ S, IsZBasis I e₀) ∧ ∀ e : Fin N → Fin I.n → I.E, IsZBasis I e → BddType I R e → ∃ e₀ ∈ S, ∃ γ : GL (Fin I.n) I.E, γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧ (∀ i j, IsIntegral ℤ ((γ : Matrix (Fin I.n) (Fin I.n) I.E) i j)) ∧ (∀ i j, IsIntegral ℤ (((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) i j)) ∧ ∀ j, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ e j = e₀ j := by
  intro I N R
  classical
  obtain ⟨c, hc0, hc⟩ := trForm_denom I
  let T := (Module.Free.ChooseBasisIndex ℤ (𝓞 I.E) → Fin N → Fin N → ℤ) × (Fin N → Fin N → ℚ)
  let has : (Fin N → Fin I.n → I.E) → T → Prop := fun e t =>
    (∀ k j, (integralBasis I.E k : I.E) • e j = ∑ i, t.1 k j i • e i) ∧ ∀ i j, trForm I (e i) (e j) = t.2 i j
  let A : Set T := (Set.univ.pi fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => {z : ℤ | |(z:ℝ)| ≤ R}) ×ˢ
    (Set.univ.pi fun _ => Set.univ.pi fun _ => {q : ℚ | |(q:ℝ)| ≤ R ∧ ∃ m : ℤ, (c:ℚ) * q = m})
  have hZ : {z : ℤ | |(z:ℝ)| ≤ R}.Finite := by
    refine (Set.finite_Icc (-⌈R⌉) ⌈R⌉).subset fun z hz => ?_
    simp only [Set.mem_setOf_eq] at hz
    have h := abs_le.mp hz
    have hR := Int.le_ceil R
    constructor
    · have : (-(⌈R⌉:ℝ)) ≤ z := by linarith
      exact_mod_cast this
    · have : (z:ℝ) ≤ ⌈R⌉ := by linarith
      exact_mod_cast this
  have hQ : {q : ℚ | |(q:ℝ)| ≤ R ∧ ∃ m : ℤ, (c:ℚ) * q = m}.Finite := by
    refine ((Set.finite_Icc (-⌈R * c⌉) ⌈R * c⌉).image fun m : ℤ => (m : ℚ) / c).subset ?_
    rintro q ⟨hq, m, hm⟩
    have hcpos : (0:ℝ) < c := by exact_mod_cast hc0
    have hmq : (m:ℝ) = c * q := by exact_mod_cast hm.symm
    have h := abs_le.mp hq
    have hR := Int.le_ceil (R * c)
    refine ⟨m, ⟨?_, ?_⟩, ?_⟩
    · have : (-(⌈R*c⌉:ℝ)) ≤ m := by rw [hmq]; nlinarith
      exact_mod_cast this
    · have : (m:ℝ) ≤ ⌈R*c⌉ := by rw [hmq]; nlinarith
      exact_mod_cast this
    · have hc' : (c:ℚ) ≠ 0 := by exact_mod_cast hc0.ne'
      simp only
      rw [← hm]; field_simp
  have hA : A.Finite := (Set.Finite.pi fun _ => Set.Finite.pi fun _ => Set.Finite.pi fun _ => hZ).prod
    (Set.Finite.pi fun _ => Set.Finite.pi fun _ => hQ)
  let pick : T → (Fin N → Fin I.n → I.E) := fun t =>
    if h : ∃ e, IsZBasis I e ∧ has e t then Classical.choose h else 0
  have hpick : ∀ t (h : ∃ e, IsZBasis I e ∧ has e t), IsZBasis I (pick t) ∧ has (pick t) t := by
    intro t h
    simp only [pick, dif_pos h]
    exact Classical.choose_spec h
  have uniq : ∀ (f : Fin N → Fin I.n → I.E) (t : T), IsZBasis I f → has f t → ∀ k j (w : Fin N → ℤ),
      (integralBasis I.E k : I.E) • f j = ∑ i, w i • f i → w = t.1 k j := by
    intro f t hf hft k j w hw
    rw [hft.1 k j] at hw
    have h0 : ∑ i, (w i - t.1 k j i) • f i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← hw, sub_self]
    funext i
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hf.1 _ h0 i)
  have compat : ∀ (f g : Fin N → Fin I.n → I.E) (t : T), IsZBasis I f → has f t → has g t →
      ∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 I.E)) (j : Fin N) (w : Fin N → ℤ),
      (integralBasis I.E k : I.E) • f j = ∑ i, w i • f i → (integralBasis I.E k : I.E) • g j = ∑ i, w i • g i := by
    intro f g t hf hft hgt k j w hw
    rw [uniq f t hf hft k j w hw]
    exact hgt.1 k j
  refine ⟨pick '' {t ∈ A | ∃ e, IsZBasis I e ∧ has e t}, (hA.subset (Set.sep_subset _ _)).image _, ?_, ?_⟩
  · rintro _ ⟨t, ⟨-, h⟩, rfl⟩
    exact (hpick t h).1
  · intro e he hb
    choose z hz hzb using hb.1
    let t : T := (z, fun i j => trForm I (e i) (e j))
    have ht : has e t := ⟨hz, fun i j => rfl⟩
    have hint : ∀ i, IntVec I (e i) := fun i => (he.2 (e i)).2 ⟨Pi.single i 1, by simp [Pi.single_apply]⟩
    have htA : t ∈ A := ⟨fun k _ j _ i _ => hzb k j i, fun i _ j _ => ⟨hb.2 i j, hc _ _ (hint i) (hint j)⟩⟩
    have hex : ∃ e', IsZBasis I e' ∧ has e' t := ⟨e, he, ht⟩
    obtain ⟨he₀, ht₀⟩ := hpick t hex
    obtain ⟨M, hMi, hMe⟩ := GlobalTheory.T.exists_integralMatrix_relating_integralVectorZBases I e (pick t) he he₀ (compat e (pick t) t he ht ht₀)
    obtain ⟨M', hM'i, hM'e⟩ := GlobalTheory.T.exists_integralMatrix_relating_integralVectorZBases I (pick t) e he₀ he (compat (pick t) e t he₀ ht₀ ht)
    have h1 : M' * M = 1 := fix_one I e _ he fun j => by rw [← Matrix.mulVec_mulVec, hMe, hM'e]
    have h2 : M * M' = 1 := (mul_eq_one_comm_of_card_eq (Fin I.n) (Fin I.n) I.E rfl).mp h1
    let γ : GL (Fin I.n) I.E := ⟨M, M', h2, h1⟩
    refine ⟨pick t, ⟨t, ⟨htA, hex⟩, rfl⟩, γ, ?_, hMi, hM'i, hMe⟩
    show Formalism.UG.cT (starRingEnd I.E) M * I.J * M = I.J
    exact GlobalTheory.T.unitary_of_preserves_hermitianTraceForm_integralBasis I e M he fun i j => by rw [hMe, hMe]; exact ht₀.2 i j

end GlobalTheory.BasesFin
