import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.IsTypeMap

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace PositivityTheory.Rg.DzCount

namespace PairingFactorsThroughPeriods

/- English proof (translation)
Unfold `ExactPer at h`. Conclude with `h.2.1`.
-/
theorem exactPer_per {q n : ℕ} {z : ℂ} (h : ExactPer q n z) : z ^ q ^ n = z := by
  unfold ExactPer at h
  exact h.2.1

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]`.
-/
theorem per_mul {q n : ℕ} {z : ℂ} (h : z ^ q ^ n = z) (k : ℕ) : z ^ q ^ (n * k) = z := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

/- English proof (translation)
Establish `key : ∀ a b : ℕ, a < b → b < n → z ^ q ^ a = z ^ q ^ b → False`. Introduce `a b hab hbn h`. Apply `hz.2.2 (b - a) (by omega) (by omega)` to reduce the goal to its premises. Establish `h1 : (z ^ q ^ a) ^ q ^ (n - a) = (z ^ q ^ b) ^ q ^ (n - a)` using `by rw [h]`. Rewrite `h1` using `[← pow_mul, ← pow_mul, ← pow_add, ← pow_add, Nat.add_sub_cancel' (by omega : a ≤ n), hz.2.1]`.

Establish `h2 : b + (n - a) = n + (b - a)` using `by omega`. Rewrite `h1` using `[h2, pow_add, pow_mul, hz.2.1]`. Conclude with `h1.symm`. Break down `lt_trichotomy a b with hab | hab | hab` into its components or cases. Conclude with `(key a b hab hb h).elim`.

Conclude with `hab`. Conclude with `(key b a hab ha h.symm).elim`.
-/
theorem per_inj {q n : ℕ} {z : ℂ} (hz : ExactPer q n z) {a b : ℕ} (ha : a < n) (hb : b < n)
    (h : z ^ q ^ a = z ^ q ^ b) : a = b := by
  have key : ∀ a b : ℕ, a < b → b < n → z ^ q ^ a = z ^ q ^ b → False := by
    intro a b hab hbn h
    apply hz.2.2 (b - a) (by omega) (by omega)
    have h1 : (z ^ q ^ a) ^ q ^ (n - a) = (z ^ q ^ b) ^ q ^ (n - a) := by rw [h]
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, Nat.add_sub_cancel' (by omega : a ≤ n),
      hz.2.1] at h1
    have h2 : b + (n - a) = n + (b - a) := by omega
    rw [h2, pow_add, pow_mul, hz.2.1] at h1
    exact h1.symm
  rcases lt_trichotomy a b with hab | hab | hab
  · exact (key a b hab hb h).elim
  · exact hab
  · exact (key b a hab ha h.symm).elim

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ' M k, Module.End.mul_apply, ih, map_smul, hv, smul_smul, pow_succ c k]`.
-/
theorem pow_apply_eig {V : Type} [AddCommGroup V] [Module ℂ V] (M : Module.End ℂ V) {v : V} {c : ℂ}
    (hv : M v = c • v) (k : ℕ) : (M ^ k) v = c ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' M k, Module.End.mul_apply, ih, map_smul, hv, smul_smul, pow_succ c k]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using hv`. Consider the case `succ k ih`. Establish `h1 : M (G ((G ^ k) v)) = G ((M ^ q) ((G ^ k) v))`. Rewrite using `[← Module.End.mul_apply M G, hMG, Module.End.mul_apply]`.

Rewrite using `[pow_succ' G k, Module.End.mul_apply, h1, pow_apply_eig M ih q, map_smul, ← pow_mul, ← pow_succ]`.
-/
theorem eig_G {V : Type} [AddCommGroup V] [Module ℂ V] {q : ℕ} (M G : Module.End ℂ V)
    (hMG : M * G = G * M ^ q) {v : V} {c : ℂ} (hv : M v = c • v) (k : ℕ) :
    M ((G ^ k) v) = c ^ q ^ k • (G ^ k) v := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    have h1 : M (G ((G ^ k) v)) = G ((M ^ q) ((G ^ k) v)) := by
      rw [← Module.End.mul_apply M G, hMG, Module.End.mul_apply]
    rw [pow_succ' G k, Module.End.mul_apply, h1, pow_apply_eig M ih q, map_smul, ← pow_mul,
      ← pow_succ]

/- English proof (translation)
Establish `hGinj : ∀ k : ℕ, Function.Injective (G ^ k)` using `fun k => ((Module.End.isUnit_iff _).mp (hG.pow k)).injective`. Take `⟨f, hf⟩ : ∃ f : Fin (m + 1) → V, ∀ j, f j = (G ^ (j : ℕ)) v` from `⟨_, fun _ => rfl⟩`. Establish `hMf : ∀ j : Fin (m + 1), M (f j) = z ^ q ^ (j : ℕ) • f j` using `fun j => by`. Rewrite using `[hf]`. Conclude with `eig_G M G hMG hv j`.

Establish `hfne : ∀ j, f j ≠ 0` using `fun j h => hv0 (hGinj (j : ℕ) (by rw [map_zero, ← hf]; exact h))`. Establish `hinj : Function.Injective (fun j : Fin (m + 1) => z ^ q ^ (j : ℕ))` using `fun a b h => Fin.ext (per_inj hz a.2 b.2 h)`. Establish `hli : LinearIndependent ℂ f` using `Module.End.eigenvectors_linearIndependent' M _ hinj f (fun j => ⟨Module.End.mem_eigenspace_iff.mpr (hMf j), hfne j⟩)`. Take `⟨b, hb⟩ : ∃ b : Module.Basis (Fin (m + 1)) ℂ V, ∀ j, b j = f j` from `⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hr]), fun j => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli _) j⟩`. Use `⟨b, fun j => by rw [hb]; exact hMf j, fun k => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hb, hb, hf, hf, Fin.val_succ, Fin.coe_castSucc, pow_succ', Module.End.mul_apply]`. Take `⟨x, hxdef⟩ : ∃ x, x = G (b (Fin.last m))` from `⟨_, rfl⟩`. Establish `hxG : x = (G ^ (m + 1)) v`. Rewrite using `[hxdef, hb, hf, Fin.val_last, pow_succ', Module.End.mul_apply]`. Establish `hx : M x = z • x`.

Rewrite using `[hxG, eig_G M G hMG hv, hz.2.1]`. Take `⟨c, hcdef⟩ : ∃ c, c = b.repr x` from `⟨_, rfl⟩`. Establish `hsum : x = ∑ j, c j • b j` using `by rw [hcdef]; exact (b.sum_repr x).symm`. Establish `hcoef : ∀ j, c j * z ^ q ^ (j : ℕ) = z * c j`. Introduce `j`.

Establish `e1 : M x = ∑ j, (c j * z ^ q ^ (j : ℕ)) • b j` using `by conv_lhs => rw [hsum]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[map_smul, hb j, hMf j, smul_smul]`. Establish `e2 : z • x = ∑ j, (z * c j) • b j` using `by conv_lhs => rw [hsum]`.

Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[smul_smul]`. Establish `e3 : (∑ j, (c j * z ^ q ^ (j : ℕ)) • b j) = ∑ j, (z * c j) • b j` using `e1.symm.trans (hx.trans e2)`. Establish `e4` using `congrArg (fun y => b.repr y j) e3`.

Simplify using `only [Module.Basis.repr_sum_self] at e4`. Conclude with `e4`. Establish `hc0 : ∀ j : Fin (m + 1), j ≠ 0 → c j = 0`. Introduce `j hj`. Establish `hjpos : 0 < (j : ℕ)` using `Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))`.

Establish `hne : z ^ q ^ (j : ℕ) ≠ z` using `hz.2.2 j hjpos j.2`. Establish `h2 : c j * (z ^ q ^ (j : ℕ) - z) = 0`. Rewrite using `[mul_sub, hcoef j]`. Expand and normalize the polynomial expressions, which then agree. Break down `mul_eq_zero.mp h2 with h | h` into its components or cases.

Conclude with `h`. Conclude with `absurd (sub_eq_zero.mp h) hne`. Establish `hx0 : x = c 0 • b 0` using `by conv_lhs => rw [hsum]`. Rewrite using `[Finset.sum_eq_single 0 (fun j _ hj => by rw [hc0 j hj, zero_smul]) (by simp)]`. Use `⟨c 0, fun h => ?_, ?_⟩` and prove the remaining obligations.

Establish `hx00 : G (b (Fin.last m)) = 0` using `by rw [← hxdef, hx0, h, zero_smul]`. Conclude with `b.ne_zero (Fin.last m) (((Module.End.isUnit_iff _).mp hG).injective (by rw [map_zero]; exact hx00))`. Rewrite using `[← hxdef]`. Conclude with `hx0`.
-/
theorem basis_side {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {q m : ℕ} (M G : Module.End ℂ V) (hG : IsUnit G) (hMG : M * G = G * M ^ q) {z : ℂ}
    (hz : ExactPer q (m + 1) z) (hr : Module.finrank ℂ V = m + 1) {v : V} (hv0 : v ≠ 0)
    (hv : M v = z • v) :
    ∃ b : Module.Basis (Fin (m + 1)) ℂ V, (∀ j : Fin (m + 1), M (b j) = z ^ q ^ (j : ℕ) • b j) ∧
      (∀ k : Fin m, G (b k.castSucc) = b k.succ) ∧
      ∃ μ : ℂ, μ ≠ 0 ∧ G (b (Fin.last m)) = μ • b 0 := by
  have hGinj : ∀ k : ℕ, Function.Injective (G ^ k) := fun k =>
    ((Module.End.isUnit_iff _).mp (hG.pow k)).injective
  obtain ⟨f, hf⟩ : ∃ f : Fin (m + 1) → V, ∀ j, f j = (G ^ (j : ℕ)) v := ⟨_, fun _ => rfl⟩
  have hMf : ∀ j : Fin (m + 1), M (f j) = z ^ q ^ (j : ℕ) • f j := fun j => by
    rw [hf]; exact eig_G M G hMG hv j
  have hfne : ∀ j, f j ≠ 0 := fun j h =>
    hv0 (hGinj (j : ℕ) (by rw [map_zero, ← hf]; exact h))
  have hinj : Function.Injective (fun j : Fin (m + 1) => z ^ q ^ (j : ℕ)) :=
    fun a b h => Fin.ext (per_inj hz a.2 b.2 h)
  have hli : LinearIndependent ℂ f :=
    Module.End.eigenvectors_linearIndependent' M _ hinj f
      (fun j => ⟨Module.End.mem_eigenspace_iff.mpr (hMf j), hfne j⟩)
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin (m + 1)) ℂ V, ∀ j, b j = f j :=
    ⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hr]),
      fun j => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli _) j⟩
  refine ⟨b, fun j => by rw [hb]; exact hMf j, fun k => ?_, ?_⟩
  · rw [hb, hb, hf, hf, Fin.val_succ, Fin.coe_castSucc, pow_succ', Module.End.mul_apply]
  · obtain ⟨x, hxdef⟩ : ∃ x, x = G (b (Fin.last m)) := ⟨_, rfl⟩
    have hxG : x = (G ^ (m + 1)) v := by
      rw [hxdef, hb, hf, Fin.val_last, pow_succ', Module.End.mul_apply]
    have hx : M x = z • x := by
      rw [hxG, eig_G M G hMG hv, hz.2.1]
    obtain ⟨c, hcdef⟩ : ∃ c, c = b.repr x := ⟨_, rfl⟩
    have hsum : x = ∑ j, c j • b j := by rw [hcdef]; exact (b.sum_repr x).symm
    have hcoef : ∀ j, c j * z ^ q ^ (j : ℕ) = z * c j := by
      intro j
      have e1 : M x = ∑ j, (c j * z ^ q ^ (j : ℕ)) • b j := by
        conv_lhs => rw [hsum]
        rw [map_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [map_smul, hb j, hMf j, smul_smul]
      have e2 : z • x = ∑ j, (z * c j) • b j := by
        conv_lhs => rw [hsum]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [smul_smul]
      have e3 : (∑ j, (c j * z ^ q ^ (j : ℕ)) • b j) = ∑ j, (z * c j) • b j :=
        e1.symm.trans (hx.trans e2)
      have e4 := congrArg (fun y => b.repr y j) e3
      simp only [Module.Basis.repr_sum_self] at e4
      exact e4
    have hc0 : ∀ j : Fin (m + 1), j ≠ 0 → c j = 0 := by
      intro j hj
      have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))
      have hne : z ^ q ^ (j : ℕ) ≠ z := hz.2.2 j hjpos j.2
      have h2 : c j * (z ^ q ^ (j : ℕ) - z) = 0 := by
        rw [mul_sub, hcoef j]
        ring
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd (sub_eq_zero.mp h) hne
    have hx0 : x = c 0 • b 0 := by
      conv_lhs => rw [hsum]
      rw [Finset.sum_eq_single 0 (fun j _ hj => by rw [hc0 j hj, zero_smul]) (by simp)]
    refine ⟨c 0, fun h => ?_, ?_⟩
    · have hx00 : G (b (Fin.last m)) = 0 := by rw [← hxdef, hx0, h, zero_smul]
      exact b.ne_zero (Fin.last m)
        (((Module.End.isUnit_iff _).mp hG).injective (by rw [map_zero]; exact hx00))
    · rw [← hxdef]
      exact hx0

end PairingFactorsThroughPeriods

open PairingFactorsThroughPeriods in
/- English proof (translation)
Unfold `St1b`. Introduce `V V' _ _ _ _ _ _ q n i M G M' G' z hn hr hr' hG hG' hMG hMG' hz hzM hzM' hdet`. Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`. Take `⟨v, hv⟩` from `hzM.exists_hasEigenvector`. Take `⟨v1, hv1⟩` from `hzM'.exists_hasEigenvector`.

Establish `hG'inj : ∀ k : ℕ, Function.Injective (G' ^ k)` using `fun k => ((Module.End.isUnit_iff _).mp (hG'.pow k)).injective`. Establish `hv1' : M' v1 = z ^ q ^ i • v1` using `Module.End.mem_eigenspace_iff.mp hv1.1`. Establish `hle : i ≤ (m + 1) * i`. Rewrite using `[add_mul, one_mul]`. Conclude with `Nat.le_add_left i (m * i)`.

Establish `hw : M' ((G' ^ ((m + 1) * i - i)) v1) = z • (G' ^ ((m + 1) * i - i)) v1`. Rewrite using `[eig_G M' G' hMG' hv1', ← pow_mul, ← pow_add, Nat.add_sub_cancel' hle, per_mul (exactPer_per hz)]`. Take `⟨b, hbM, hbG, μ, hμ, hbl⟩` from `basis_side M G hG hMG hz hr hv.2 (Module.End.mem_eigenspace_iff.mp hv.1)`. Take `⟨b', hbM', hbG', μ', hμ', hbl'⟩` from `basis_side M' G' hG' hMG' hz hr' (fun h => hv1.2 (hG'inj _ (by rw [map_zero]; exact h))) hw`. Take `⟨T, hT⟩ : ∃ T : V ≃ₗ[ℂ] V', ∀ j, T (b j) = b' j` from `⟨b.equiv b' (Equiv.refl _), fun j => by simp⟩`.

Establish `hTs : ∀ j, T.symm (b' j) = b j` using `fun j => by rw [← hT j, LinearEquiv.symm_apply_apply]`. Take `⟨G'', hG''⟩ : ∃ G'' : Module.End ℂ V, G'' = T.symm.toLinearMap ∘ₗ G' ∘ₗ T.toLinearMap` from `⟨_, rfl⟩`. Establish `hdet'' : LinearMap.det G'' = LinearMap.det G'`. Rewrite using `[hG'']`. Establish `h` using `LinearMap.det_conj G' T.symm`.

Simplify using `using h`. Take `⟨d, hd⟩ : ∃ d : Fin (m + 1) → ℂ, d = fun j => if j = Fin.last m then μ / μ' else 1` from `⟨_, rfl⟩`. Take `⟨D, hDdef⟩ : ∃ D : Module.End ℂ V, D = Matrix.toLin b b (Matrix.diagonal d)` from `⟨_, rfl⟩`. Establish `hD : ∀ j, D (b j) = d j • b j` using `fun j => by`. Rewrite using `[hDdef, Matrix.toLin_self]`.

Simplify using `[Matrix.diagonal_apply]`. Establish `hGD : G = G'' ∘ₗ D`. Apply `b.ext` to reduce the goal to its premises. Introduce `j`. Rewrite using `[LinearMap.comp_apply, hD j, map_smul, hG'']`.

Break down `Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl` into its components or cases. Establish `h1 : d k.castSucc = 1`. Rewrite using `[hd]`. Simplify using `[Fin.castSucc_lt_last k |>.ne]`. Rewrite using `[h1, one_smul]`.

Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[hT, hbG', hTs, hbG]`. Establish `h1 : d (Fin.last m) = μ / μ'` using `by rw [hd]; simp`. Rewrite using `[h1]`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`.

Rewrite using `[hT, hbl', map_smul, hTs, smul_smul, div_mul_cancel₀ μ hμ', hbl]`. Establish `hdetD : LinearMap.det D = μ / μ'`. Rewrite using `[hDdef, LinearMap.det_toLin, Matrix.det_diagonal, hd]`. Simplify using the standard rewrite rules. Establish `hμμ : μ = μ'`.

Establish `h1 : LinearMap.det G = LinearMap.det G' * (μ / μ')`. Rewrite using `[hGD, LinearMap.det_comp, hdet'', hdetD]`. Establish `hne : LinearMap.det G' ≠ 0` using `(hG'.map LinearMap.det).ne_zero`. Rewrite `h1` using `[hdet]`. Establish `h2 : μ / μ' = 1` using `mul_left_cancel₀ hne (by rw [mul_one]; exact h1.symm)`.

Conclude with `(div_eq_one_iff_eq hμ').mp h2`. Use `⟨T, fun v => ?_, fun v => ?_⟩` and prove the remaining obligations. Establish `h : T.toLinearMap ∘ₗ M = M' ∘ₗ T.toLinearMap`. Apply `b.ext` to reduce the goal to its premises. Introduce `j`.

Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[hbM, map_smul, hT, hbM']`. Conclude with `LinearMap.congr_fun h v`. Establish `h : T.toLinearMap ∘ₗ G = G' ∘ₗ T.toLinearMap`. Apply `b.ext` to reduce the goal to its premises.

Introduce `j`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`. Break down `Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl` into its components or cases. Rewrite using `[hbG, hT, hT, hbG']`. Rewrite using `[hbl, map_smul, hT, hT, hbl', hμμ]`.

Conclude with `LinearMap.congr_fun h v`.
-/
theorem st1b : St1b := by
  unfold St1b
  intro V V' _ _ _ _ _ _ q n i M G M' G' z hn hr hr' hG hG' hMG hMG' hz hzM hzM' hdet
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨v, hv⟩ := hzM.exists_hasEigenvector
  obtain ⟨v1, hv1⟩ := hzM'.exists_hasEigenvector
  have hG'inj : ∀ k : ℕ, Function.Injective (G' ^ k) := fun k =>
    ((Module.End.isUnit_iff _).mp (hG'.pow k)).injective
  have hv1' : M' v1 = z ^ q ^ i • v1 := Module.End.mem_eigenspace_iff.mp hv1.1
  have hle : i ≤ (m + 1) * i := by
    rw [add_mul, one_mul]
    exact Nat.le_add_left i (m * i)
  have hw : M' ((G' ^ ((m + 1) * i - i)) v1) = z • (G' ^ ((m + 1) * i - i)) v1 := by
    rw [eig_G M' G' hMG' hv1', ← pow_mul, ← pow_add, Nat.add_sub_cancel' hle,
      per_mul (exactPer_per hz)]
  obtain ⟨b, hbM, hbG, μ, hμ, hbl⟩ :=
    basis_side M G hG hMG hz hr hv.2 (Module.End.mem_eigenspace_iff.mp hv.1)
  obtain ⟨b', hbM', hbG', μ', hμ', hbl'⟩ :=
    basis_side M' G' hG' hMG' hz hr'
      (fun h => hv1.2 (hG'inj _ (by rw [map_zero]; exact h))) hw
  obtain ⟨T, hT⟩ : ∃ T : V ≃ₗ[ℂ] V', ∀ j, T (b j) = b' j :=
    ⟨b.equiv b' (Equiv.refl _), fun j => by simp⟩
  have hTs : ∀ j, T.symm (b' j) = b j := fun j => by rw [← hT j, LinearEquiv.symm_apply_apply]
  obtain ⟨G'', hG''⟩ : ∃ G'' : Module.End ℂ V,
      G'' = T.symm.toLinearMap ∘ₗ G' ∘ₗ T.toLinearMap := ⟨_, rfl⟩
  have hdet'' : LinearMap.det G'' = LinearMap.det G' := by
    rw [hG'']
    have h := LinearMap.det_conj G' T.symm
    simpa using h
  obtain ⟨d, hd⟩ : ∃ d : Fin (m + 1) → ℂ, d = fun j => if j = Fin.last m then μ / μ' else 1 :=
    ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : Module.End ℂ V, D = Matrix.toLin b b (Matrix.diagonal d) := ⟨_, rfl⟩
  have hD : ∀ j, D (b j) = d j • b j := fun j => by
    rw [hDdef, Matrix.toLin_self]
    simp [Matrix.diagonal_apply]
  have hGD : G = G'' ∘ₗ D := by
    apply b.ext
    intro j
    rw [LinearMap.comp_apply, hD j, map_smul, hG'']
    rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
    · have h1 : d k.castSucc = 1 := by
        rw [hd]
        simp [Fin.castSucc_lt_last k |>.ne]
      rw [h1, one_smul]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hT, hbG', hTs, hbG]
    · have h1 : d (Fin.last m) = μ / μ' := by rw [hd]; simp
      rw [h1]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hT, hbl', map_smul, hTs, smul_smul, div_mul_cancel₀ μ hμ', hbl]
  have hdetD : LinearMap.det D = μ / μ' := by
    rw [hDdef, LinearMap.det_toLin, Matrix.det_diagonal, hd]
    simp
  have hμμ : μ = μ' := by
    have h1 : LinearMap.det G = LinearMap.det G' * (μ / μ') := by
      rw [hGD, LinearMap.det_comp, hdet'', hdetD]
    have hne : LinearMap.det G' ≠ 0 := (hG'.map LinearMap.det).ne_zero
    rw [hdet] at h1
    have h2 : μ / μ' = 1 := mul_left_cancel₀ hne (by rw [mul_one]; exact h1.symm)
    exact (div_eq_one_iff_eq hμ').mp h2
  refine ⟨T, fun v => ?_, fun v => ?_⟩
  · have h : T.toLinearMap ∘ₗ M = M' ∘ₗ T.toLinearMap := by
      apply b.ext
      intro j
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hbM, map_smul, hT, hbM']
    exact LinearMap.congr_fun h v
  · have h : T.toLinearMap ∘ₗ G = G' ∘ₗ T.toLinearMap := by
      apply b.ext
      intro j
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
      · rw [hbG, hT, hT, hbG']
      · rw [hbl, map_smul, hT, hT, hbl', hμμ]
    exact LinearMap.congr_fun h v

end PositivityTheory.Rg.DzCount

end
