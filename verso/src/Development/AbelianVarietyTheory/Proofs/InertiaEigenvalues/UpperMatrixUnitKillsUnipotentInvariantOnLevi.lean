import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DiscreteSpectrumResidual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

noncomputable section

namespace GlobalTheory.UnipKill

open Matrix

section General

variable {R S : Type} [CommRing R] [CommRing S] {α : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] {N : ℕ}

/- English proof (translation)
Rewrite `hg`, the goal using `[mem_unipRad]`. Establish `hval : ∀ i j, ((cornerGL N s g : GL (Fin N) S) : Matrix (Fin N) (Fin N) S) i j = (1 : Matrix (Fin N) (Fin N) S) i j - s ((1 : Matrix (Fin N) (Fin N) R) i j) + s ((g : Matrix (Fin N) (Fin N) R) i j)` using `fun i j => rfl`. Use `⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩` and prove the remaining obligations. Establish `hne : i ≠ j` using `by rintro rfl; exact lt_irrefl _ hij`. Rewrite using `[hval, mem_parab.1 hg.1 i j hij]`.

Simplify using `[Matrix.one_apply_ne hne]`. Rewrite using `[hval, hg.2 a i j]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules.

Establish `hne : e ⟨a, i⟩ ≠ e ⟨a, j⟩` using `fun h => hij (by simpa using e.injective h)`. Simplify using `[Matrix.one_apply_ne hne, Matrix.one_apply_ne hij]`.
-/
theorem cornerGL_mem_unipRad (s : R →ₙ+* S) (e : (Σ a, m a) ≃ Fin N) {g : GL (Fin N) R}
    (hg : g ∈ unipRad R e) : cornerGL N s g ∈ unipRad S e := by
  rw [mem_unipRad] at hg ⊢
  have hval : ∀ i j, ((cornerGL N s g : GL (Fin N) S) : Matrix (Fin N) (Fin N) S) i j =
      (1 : Matrix (Fin N) (Fin N) S) i j - s ((1 : Matrix (Fin N) (Fin N) R) i j) +
        s ((g : Matrix (Fin N) (Fin N) R) i j) := fun i j => rfl
  refine ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩
  · have hne : i ≠ j := by rintro rfl; exact lt_irrefl _ hij
    rw [hval, mem_parab.1 hg.1 i j hij]
    simp [Matrix.one_apply_ne hne]
  · rw [hval, hg.2 a i j]
    by_cases hij : i = j
    · subst hij; simp
    · have hne : e ⟨a, i⟩ ≠ e ⟨a, j⟩ := fun h => hij (by simpa using e.injective h)
      simp [Matrix.one_apply_ne hne, Matrix.one_apply_ne hij]

omit [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in

def tv {p q : Fin N} (hpq : p ≠ q) (c : R) : GL (Fin N) R :=
  ⟨transvection p q c, transvection p q (-c),
    (transvection_mul_transvection_same p q hpq c (-c)).trans (by rw [add_neg_cancel, transvection_zero]),
    (transvection_mul_transvection_same p q hpq (-c) c).trans (by rw [neg_add_cancel, transvection_zero])⟩

omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in

/- English proof (translation)
Introduce and unpack `rfl`. Conclude with `lt_irrefl _ hpq`.
-/
theorem ne_of_blk_lt (e : (Σ a, m a) ≃ Fin N) {p q : Fin N} (hpq : blk e p < blk e q) : p ≠ q := by
  rintro rfl; exact lt_irrefl _ hpq

/- English proof (translation)
Rewrite using `[mem_unipRad]`. Use `⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩` and prove the remaining obligations. Establish `hne : i ≠ j` using `by rintro rfl; exact lt_irrefl _ hij`. Express the relevant statement in the definitionally equal form `(transvection p q c) i j = 0`. Rewrite using `[transvection, Matrix.add_apply, Matrix.one_apply_ne hne, Matrix.single_apply]`.

Rewrite using `[if_neg, zero_add]`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `lt_asymm hpq hij`. Express the relevant statement in the definitionally equal form `(transvection p q c) (e ⟨a, i⟩) (e ⟨a, j⟩) = _`. Rewrite using `[transvection, Matrix.add_apply, Matrix.single_apply, if_neg, add_zero]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Establish `hne : e ⟨a, i⟩ ≠ e ⟨a, j⟩` using `fun h => hij (by simpa using e.injective h)`. Rewrite using `[Matrix.one_apply_ne hne, Matrix.one_apply_ne hij]`.

Introduce and unpack `⟨h1, h2⟩`. Establish `h1' : blk e p = a` using `by rw [h1]; simp`. Establish `h2' : blk e q = a` using `by rw [h2]; simp`. Rewrite `hpq` using `[h1', h2']`. Conclude with `lt_irrefl _ hpq`.
-/
theorem tv_mem_unipRad (e : (Σ a, m a) ≃ Fin N) {p q : Fin N} (hpq : blk e p < blk e q) (c : R) :
    tv (ne_of_blk_lt e hpq) c ∈ unipRad R e := by
  rw [mem_unipRad]
  refine ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩
  · have hne : i ≠ j := by rintro rfl; exact lt_irrefl _ hij
    change (transvection p q c) i j = 0
    rw [transvection, Matrix.add_apply, Matrix.one_apply_ne hne, Matrix.single_apply]
    rw [if_neg, zero_add]
    rintro ⟨rfl, rfl⟩
    exact lt_asymm hpq hij
  · change (transvection p q c) (e ⟨a, i⟩) (e ⟨a, j⟩) = _
    rw [transvection, Matrix.add_apply, Matrix.single_apply, if_neg, add_zero]
    · by_cases hij : i = j
      · subst hij; simp
      · have hne : e ⟨a, i⟩ ≠ e ⟨a, j⟩ := fun h => hij (by simpa using e.injective h)
        rw [Matrix.one_apply_ne hne, Matrix.one_apply_ne hij]
    · rintro ⟨h1, h2⟩
      have h1' : blk e p = a := by rw [h1]; simp
      have h2' : blk e q = a := by rw [h2]; simp
      rw [h1', h2'] at hpq
      exact lt_irrefl _ hpq

end General

section Adelic

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Express the relevant statement in the definitionally equal form `(transvection p q (t • x)) i j = (1 : Matrix (Fin N) (Fin N) (Cinf E)) i j + t • (Matrix.single p q x) i j`. Rewrite using `[transvection, Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem toL_tv {p q : Fin N} (hpq : p ≠ q) (x : Cinf E) (t : ℝ) :
    toL ((tv hpq (t • x) : GL (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E)) =
      oneL E N + t • toL (Matrix.single p q x) := by
  funext i j
  change (transvection p q (t • x)) i j = (1 : Matrix (Fin N) (Fin N) (Cinf E)) i j + t • (Matrix.single p q x) i j
  rw [transvection, Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
  split_ifs <;> simp

/- English proof (translation)
Use `set e := stdBlocks n h`. Use `set g := leviEmb (Ad E) e m`. Establish `hne` using `ne_of_blk_lt e hpq`. Set `u : ℝ → GL (Fin N) (Cinf E)` to `fun t => tv hne (t • x)`. Establish `hu0 : u 0 = 1` using `Units.ext (by show transvection p q ((0 : ℝ) • x) = 1`.

Rewrite using `[zero_smul, transvection_zero])`. Establish `hline : HasDerivAt (fun t => toL (u t).val) (toL (Matrix.single p q x)) 0`. Establish `: (fun t => toL (u t).val) = fun t : ℝ => oneL E N + t • toL (Matrix.single p q x)`. Use function extensionality and compare the values at `fun t => toL_tv hne x t`. Rewrite using `[this]`.

Simplify using `using ((hasDerivAt_id (0 : ℝ)).smul_const (toL (Matrix.single p q x))).const_add (oneL E N)`. Establish `hc` using `hasDerivAt_curve ψ g u (toL (Matrix.single p q x)) hu0 hline`. Establish `hconst : (fun t => ψ.1 (g * infGL E N (u t))) = fun _ => ψ.1 g`. Use function extensionality and compare the values at `t`. Establish `hv : infGL E N (u t) ∈ unipRad (Ad E) e` using `cornerGL_mem_unipRad (sInf E) e (tv_mem_unipRad e hpq _)`.

Establish `hw : g * infGL E N (u t) * g⁻¹ ∈ unipRad (Ad E) e` using `(Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer (Ad E) e m) _).1 hv`. Rewrite using `[← hψ _ hw g, inv_mul_cancel_right]`. Rewrite `hc` using `[hconst]`. Conclude with `hc.unique (hasDerivAt_const 0 _)`.
-/
theorem lieD_single_leviEmb {c : ℕ} {n : Fin c → ℕ} (h : ∑ i, n i = N) (ψ : Sm E N)
    (hψ : ∀ u ∈ unipRad (Ad E) (stdBlocks n h), ∀ g, ψ.1 (u * g) = ψ.1 g) {p q : Fin N}
    (hpq : blk (stdBlocks n h) p < blk (stdBlocks n h) q) (x : Cinf E) (m : Levi (Ad E) fun i => Fin (n i)) :
    lieD (toL (Matrix.single p q x)) ψ.1 (leviEmb (Ad E) (stdBlocks n h) m) = 0 := by
  set e := stdBlocks n h
  set g := leviEmb (Ad E) e m
  have hne := ne_of_blk_lt e hpq
  let u : ℝ → GL (Fin N) (Cinf E) := fun t => tv hne (t • x)
  have hu0 : u 0 = 1 := Units.ext (by
    show transvection p q ((0 : ℝ) • x) = 1
    rw [zero_smul, transvection_zero])
  have hline : HasDerivAt (fun t => toL (u t).val) (toL (Matrix.single p q x)) 0 := by
    have : (fun t => toL (u t).val) = fun t : ℝ => oneL E N + t • toL (Matrix.single p q x) :=
      funext fun t => toL_tv hne x t
    rw [this]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (toL (Matrix.single p q x))).const_add (oneL E N)
  have hc := hasDerivAt_curve ψ g u (toL (Matrix.single p q x)) hu0 hline
  have hconst : (fun t => ψ.1 (g * infGL E N (u t))) = fun _ => ψ.1 g := by
    funext t
    have hv : infGL E N (u t) ∈ unipRad (Ad E) e := cornerGL_mem_unipRad (sInf E) e (tv_mem_unipRad e hpq _)
    have hw : g * infGL E N (u t) * g⁻¹ ∈ unipRad (Ad E) e :=
      (Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer (Ad E) e m) _).1 hv
    rw [← hψ _ hw g, inv_mul_cancel_right]
  rw [hconst] at hc
  exact hc.unique (hasDerivAt_const 0 _)

end Adelic

open Complex in

/- English proof (translation)
Establish `key` using `fun x => lieD_single_leviEmb h ψ hψ hpq x m`. Express the relevant statement in the definitionally equal form `((1 / 2 : ℂ) • (lieS E N p q (atEmb τ 1) - Complex.I • lieS E N p q (atEmb τ Complex.I)) ψ).1 _ = 0`. Simplify using `only [LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply, Pi.sub_apply, lieS_apply, CuspRep.lie_apply, key, smul_zero, sub_zero]`.
-/
theorem eop_leviEmb_eq_zero (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ)
    (h : ∑ i, n i = N) (ψ : Sm E N) (hψ : ∀ u ∈ unipRad (Ad E) (stdBlocks n h), ∀ g, ψ.1 (u * g) = ψ.1 g)
    (τ : E →+* ℂ) (p q : Fin N) (hpq : blk (stdBlocks n h) p < blk (stdBlocks n h) q) (m) :
    (Eop τ p q ψ).1 (leviEmb (Ad E) (stdBlocks n h) m) = 0 := by
  have key := fun x => lieD_single_leviEmb h ψ hψ hpq x m
  change ((1 / 2 : ℂ) • (lieS E N p q (atEmb τ 1) - Complex.I • lieS E N p q (atEmb τ Complex.I)) ψ).1 _ = 0
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply,
    Pi.sub_apply, lieS_apply, CuspRep.lie_apply, key, smul_zero, sub_zero]

end GlobalTheory.UnipKill
