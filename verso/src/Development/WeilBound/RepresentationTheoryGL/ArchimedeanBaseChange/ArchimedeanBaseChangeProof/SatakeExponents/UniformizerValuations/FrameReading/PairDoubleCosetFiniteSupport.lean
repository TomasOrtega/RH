import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.JoinType
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeIntegralFiniteSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriHeckeSumAdditiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportConvolutionTripleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportProductQuotientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumCosetSmulLinear
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeSumInvariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriDoubleCosetFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleParabolicInductionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalFixedTensorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsJointEigenvectorNonzeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativeCharacterOnConeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdRelIndexNeZeroStatement

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.Tail

section Gen

variable {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Simplify using `[GlobalTheory.PRep.fixed, GlobalTheory.PRep.eig]`.
-/
theorem mem_fixed_iff' (ρ : Representation ℂ Γ V) (K : Subgroup Γ) (v : V) :
    v ∈ GlobalTheory.PRep.fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  simp [GlobalTheory.PRep.fixed, GlobalTheory.PRep.eig]

/- English proof (translation)
Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises. Introduce `q hq`. Apply `hs` to reduce the goal to its premises. Introduce `h0`. Apply `hq` to reduce the goal to its premises.

Simplify using `[h0]`.
-/
theorem hsum_eq (ρ : Representation ℂ Γ V) (K : Subgroup Γ) (f : Γ → ℂ) {s : Finset (Γ ⧸ K)}
    (hs : (Function.support fun q : Γ ⧸ K => f q.out) ⊆ s) (v : V) :
    ∑ᶠ q : Γ ⧸ K, f q.out • ρ q.out v = ∑ q ∈ s, f q.out • ρ q.out v := by
  apply finsum_eq_sum_of_support_subset
  intro q hq
  apply hs
  intro h0
  apply hq
  simp [h0]

/- English proof (translation)
Rewrite using `[hsum_eq ρ K f hfin.coe_toFinset.ge v, LinearMap.sum_apply]`. Both sides reduce to the same expression.
-/
theorem hk_apply_sum (ρ : Representation ℂ Γ V) (K : Subgroup Γ) (f : Γ → ℂ)
    (hfin : (Function.support fun q : Γ ⧸ K => f q.out).Finite) (v : V) :
    (∑ q ∈ hfin.toFinset, f q.out • ρ q.out) v = ∑ᶠ q : Γ ⧸ K, f q.out • ρ q.out v := by
  rw [hsum_eq ρ K f hfin.coe_toFinset.ge v, LinearMap.sum_apply]
  rfl

/- English proof (translation)
Introduce `v hv`. Rewrite using `[hk_apply_sum]`. Conclude with `(mem_fixed_iff' ρ K _).2 (GlobalTheory.T.hecke_sum_invariant Γ V ρ K f hfin hbi v ((mem_fixed_iff' ρ K v).1 hv))`.
-/
theorem hk_mapsTo (ρ : Representation ℂ Γ V) (K : Subgroup Γ) (f : Γ → ℂ)
    (hfin : (Function.support fun q : Γ ⧸ K => f q.out).Finite)
    (hbi : ∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) :
    ∀ v ∈ GlobalTheory.PRep.fixed ρ K, (∑ q ∈ hfin.toFinset, f q.out • ρ q.out) v ∈ GlobalTheory.PRep.fixed ρ K := by
  intro v hv
  rw [hk_apply_sum]
  exact (mem_fixed_iff' ρ K _).2 (GlobalTheory.T.hecke_sum_invariant Γ V ρ K f hfin hbi v ((mem_fixed_iff' ρ K v).1 hv))

def hkW (ρ : Representation ℂ Γ V) (K : Subgroup Γ) (f : Γ → ℂ)
    (hfin : (Function.support fun q : Γ ⧸ K => f q.out).Finite)
    (hbi : ∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) : Module.End ℂ (GlobalTheory.PRep.fixed ρ K) :=
  (∑ q ∈ hfin.toFinset, f q.out • ρ q.out).restrict (hk_mapsTo ρ K f hfin hbi)

/- English proof (translation)
Rewrite using `[← hk_apply_sum ρ K f hfin]`. Both sides reduce to the same expression.
-/
theorem hkW_apply (ρ : Representation ℂ Γ V) (K : Subgroup Γ) (f : Γ → ℂ)
    (hfin : (Function.support fun q : Γ ⧸ K => f q.out).Finite)
    (hbi : ∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) (v : GlobalTheory.PRep.fixed ρ K) :
    ((hkW ρ K f hfin hbi v : GlobalTheory.PRep.fixed ρ K) : V) = ∑ᶠ q : Γ ⧸ K, f q.out • ρ q.out (v : V) := by
  rw [← hk_apply_sum ρ K f hfin]
  rfl

variable [TopologicalSpace Γ]

/- English proof (translation)
Introduce `r`. Proceed by induction on `r with`. Consider the case `zero => exact ⟨hGS, hGI, rfl⟩`. Consider the case `succ r ih`. Take `⟨h1, h2, h3⟩` from `ih`.

Establish `hsm : SmVec R (A^[r] G)` using `⟨I, hI, (mem_fixed_iff' R I _).2 h2⟩`. Establish `hfix` using `GlobalTheory.T.hecke_sum_invariant Γ X R I f hfin hbi (A^[r] G) h2`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply', hA _ h2, ← h3]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Apply `S.smul_mem` to reduce the goal to its premises.

Rewrite using `[hsum_eq R I f hfin.coe_toFinset.ge]`. Conclude with `S.sum_mem fun q _ => S.smul_mem _ (hS _ _ h1)`. Introduce `k hk`. Rewrite using `[map_smul, hfix k hk]`. Rewrite using `[map_smul, hsum_eq R I f hfin.coe_toFinset.ge, hsum_eq ρ I f hfin.coe_toFinset.ge, map_sum]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hL _ _ h1 hsm]`.
-/
theorem iter_push {X : Type} [AddCommGroup X] [Module ℂ X]
    (R : Representation ℂ Γ X) (S : Submodule ℂ X) (ρ : Representation ℂ Γ V) (Lj : X →ₗ[ℂ] V)
    (hS : ∀ g, ∀ x ∈ S, R g x ∈ S) (hL : ∀ g, ∀ x ∈ S, SmVec R x → Lj (R g x) = ρ g (Lj x))
    (I : Subgroup Γ) (hI : IsOpen (I : Set Γ)) (f : Γ → ℂ)
    (hfin : (Function.support fun q : Γ ⧸ I => f q.out).Finite)
    (hbi : ∀ k ∈ I, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) (κ : ℂ) (A : X → X)
    (hA : ∀ F, (∀ k ∈ I, R k F = F) → A F = κ • ∑ᶠ q : Γ ⧸ I, f q.out • R q.out F)
    (G : X) (hGS : G ∈ S) (hGI : ∀ k ∈ I, R k G = G) : ∀ r : ℕ,
    A^[r] G ∈ S ∧ (∀ k ∈ I, R k (A^[r] G) = A^[r] G) ∧
      Lj (A^[r] G) = (fun v => κ • ∑ᶠ q : Γ ⧸ I, f q.out • ρ q.out v)^[r] (Lj G) := by
  intro r
  induction r with
  | zero => exact ⟨hGS, hGI, rfl⟩
  | succ r ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hsm : SmVec R (A^[r] G) := ⟨I, hI, (mem_fixed_iff' R I _).2 h2⟩
    have hfix := GlobalTheory.T.hecke_sum_invariant Γ X R I f hfin hbi (A^[r] G) h2
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hA _ h2, ← h3]
    refine ⟨?_, ?_, ?_⟩
    · apply S.smul_mem
      rw [hsum_eq R I f hfin.coe_toFinset.ge]
      exact S.sum_mem fun q _ => S.smul_mem _ (hS _ _ h1)
    · intro k hk
      rw [map_smul, hfix k hk]
    · rw [map_smul, hsum_eq R I f hfin.coe_toFinset.ge, hsum_eq ρ I f hfin.coe_toFinset.ge, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_smul, hL _ _ h1 hsm]

end Gen

/- English proof (translation)
Introduce `k hk g`. Establish `e1 : (∃ x ∈ iwGL N w, ∃ z ∈ iwGL N w, k * g = x * t * z) ↔ ∃ x ∈ iwGL N w, ∃ z ∈ iwGL N w, g = x * t * z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, z, hz, e⟩`. Use `⟨k⁻¹ * x, mul_mem (inv_mem hk) hx, z, hz, ?_⟩` and prove the remaining obligations.

Rewrite using `[show g = k⁻¹ * (k * g) by group, e]`. Use `group`. Introduce and unpack `⟨x, hx, z, hz, e⟩`. Conclude with `⟨k * x, mul_mem hk hx, z, hz, by rw [e]; group⟩`. Establish `e2 : (∃ x ∈ iwGL N w, ∃ z ∈ iwGL N w, g * k = x * t * z) ↔ ∃ x ∈ iwGL N w, ∃ z ∈ iwGL N w, g = x * t * z`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, z, hz, e⟩`. Use `⟨x, hx, z * k⁻¹, mul_mem hz (inv_mem hk), ?_⟩` and prove the remaining obligations. Rewrite using `[show g = g * k * k⁻¹ by group, e]`. Use `group`.

Introduce and unpack `⟨x, hx, z, hz, e⟩`. Conclude with `⟨x, hx, z * k, mul_mem hz hk, by rw [e]; group⟩`. Unfold `dcos`. Prove the components needed by the constructor for the conclusion. Distinguish the cases in `h : ∃ x ∈ iwGL N w, ∃ z ∈ iwGL N w, g = x * t * z`.

Rewrite using `[if_pos (e1.2 h), if_pos h]`. Rewrite using `[if_neg (fun h' => h (e1.1 h')), if_neg h]`. Distinguish the cases in `h : ∃ x ∈ iwGL N w, ∃ z ∈ iwGL N w, g = x * t * z`. Rewrite using `[if_pos (e2.2 h), if_pos h]`. Rewrite using `[if_neg (fun h' => h (e2.1 h')), if_neg h]`.
-/
theorem dcos_inv {E : Type} [Field E] [NumberField E] [IsCMField E] (N : ℕ) (w : Pl E) (t : GLw N w) :
    ∀ k ∈ iwGL N w, ∀ g, dcos N w t (k * g) = dcos N w t g ∧ dcos N w t (g * k) = dcos N w t g := by
  intro k hk g
  have e1 : (∃ x ∈ iwGL N w, ∃ z ∈ iwGL N w, k * g = x * t * z) ↔
      ∃ x ∈ iwGL N w, ∃ z ∈ iwGL N w, g = x * t * z := by
    constructor
    · rintro ⟨x, hx, z, hz, e⟩
      refine ⟨k⁻¹ * x, mul_mem (inv_mem hk) hx, z, hz, ?_⟩
      rw [show g = k⁻¹ * (k * g) by group, e]
      group
    · rintro ⟨x, hx, z, hz, e⟩
      exact ⟨k * x, mul_mem hk hx, z, hz, by rw [e]; group⟩
  have e2 : (∃ x ∈ iwGL N w, ∃ z ∈ iwGL N w, g * k = x * t * z) ↔
      ∃ x ∈ iwGL N w, ∃ z ∈ iwGL N w, g = x * t * z := by
    constructor
    · rintro ⟨x, hx, z, hz, e⟩
      refine ⟨x, hx, z * k⁻¹, mul_mem hz (inv_mem hk), ?_⟩
      rw [show g = g * k * k⁻¹ by group, e]
      group
    · rintro ⟨x, hx, z, hz, e⟩
      exact ⟨x, hx, z * k, mul_mem hz hk, by rw [e]; group⟩
  unfold dcos
  constructor
  · by_cases h : ∃ x ∈ iwGL N w, ∃ z ∈ iwGL N w, g = x * t * z
    · rw [if_pos (e1.2 h), if_pos h]
    · rw [if_neg (fun h' => h (e1.1 h')), if_neg h]
  · by_cases h : ∃ x ∈ iwGL N w, ∃ z ∈ iwGL N w, g = x * t * z
    · rw [if_pos (e2.2 h), if_pos h]
    · rw [if_neg (fun h' => h (e2.1 h')), if_neg h]

/- English proof (translation)
Introduce `i j hij`. Break down `hij.lt_or_eq with hlt | rfl` into its components or cases. Use `h i j hlt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `le_rfl`.
-/
theorem gap_anti {N : ℕ} {x : Fin N → ℤ} (h : Gap x) : Antitone x := by
  intro i j hij
  rcases hij.lt_or_eq with hlt | rfl
  · have := h i j hlt
    omega
  · exact le_rfl

/- English proof (translation)
Introduce `i j hij`. Use `h i j hij` as an intermediate fact. Use `h' i j hij` as an intermediate fact. Simplify using `only [Pi.add_apply]`. Use linear arithmetic over natural numbers and integers.
-/
theorem gap_add {N : ℕ} {x x' : Fin N → ℤ} (h : Gap x) (h' : Gap x') : Gap (x + x') := by
  intro i j hij
  have := h i j hij
  have := h' i j hij
  simp only [Pi.add_apply]
  omega

section Place

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

/- English proof (translation)
The claim follows from `GlobalTheory.T.finite_support_product_quotient _ _ _ _ _ _ (GlobalTheory.T.iwahori_double_coset_finite E w a _).1 (GlobalTheory.T.iwahori_double_coset_finite E w b _).1 (fun k hk g => (dcos_inv a w _ k hk g).2) (fun k hk g => (dcos_inv b w _ k hk g).2)`.
-/
theorem pair_double_coset_finite_support (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (x : Fin a → ℤ) (y : Fin b → ℤ) :
    (Function.support fun q : (GLw a w × GLw b w) ⧸ I2 a b w => dc2 w ϖ x y q.out).Finite :=
  GlobalTheory.T.finite_support_product_quotient _ _ _ _ _ _ (GlobalTheory.T.iwahori_double_coset_finite E w a _).1 (GlobalTheory.T.iwahori_double_coset_finite E w b _).1
    (fun k hk g => (dcos_inv a w _ k hk g).2) (fun k hk g => (dcos_inv b w _ k hk g).2)

/- English proof (translation)
Introduce `k hk g`. Take `⟨hk1, hk2⟩` from `Subgroup.mem_prod.1 hk`. Simplify using `only [dc2, Prod.fst_mul, Prod.snd_mul, (dcos_inv a w (tdiag ϖ x) k.1 hk1 g.1).1, (dcos_inv a w (tdiag ϖ x) k.1 hk1 g.1).2, (dcos_inv b w (tdiag ϖ y) k.2 hk2 g.2).1, (dcos_inv b w (tdiag ϖ y) k.2 hk2 g.2).2, and_self]`.
-/
theorem pair_double_coset_bi_invariant (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (x : Fin a → ℤ) (y : Fin b → ℤ) :
    ∀ k ∈ I2 a b w, ∀ g, dc2 w ϖ x y (k * g) = dc2 w ϖ x y g ∧ dc2 w ϖ x y (g * k) = dc2 w ϖ x y g := by
  intro k hk g
  obtain ⟨hk1, hk2⟩ := Subgroup.mem_prod.1 hk
  simp only [dc2, Prod.fst_mul, Prod.snd_mul, (dcos_inv a w (tdiag ϖ x) k.1 hk1 g.1).1,
    (dcos_inv a w (tdiag ϖ x) k.1 hk1 g.1).2, (dcos_inv b w (tdiag ϖ y) k.2 hk2 g.2).1,
    (dcos_inv b w (tdiag ϖ y) k.2 hk2 g.2).2, and_self]

/- English proof (translation)
Unfold `qh`. Establish `: (0 : ℝ) < (qV E w : ℝ)` using `by exact_mod_cast Nat.pos_of_ne_zero (GlobalTheory.LFun.qV_ne_zero w)`. Conclude with `(Real.sqrt_pos.2 this).ne'` after adjusting the coercions.
-/
theorem qh_ne (w : Pl E) : qh w ≠ 0 := by
  unfold qh
  have : (0 : ℝ) < (qV E w : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (GlobalTheory.LFun.qV_ne_zero w)
  exact_mod_cast (Real.sqrt_pos.2 this).ne'

/- English proof (translation)
Establish `hIa` using `GlobalTheory.T.iwahori_double_coset_finite E w a`. Establish `hIb` using `GlobalTheory.T.iwahori_double_coset_finite E w b`. Establish `hmul : ∀ (x x' : Fin a → ℤ) (y y' : Fin b → ℤ), Gap x → Gap x' → Gap y → Gap y' → hkW ρ (I2 a b w) (dc2 w ϖ (x + x') (y + y')) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _) = hkW ρ (I2 a b w) (dc2 w ϖ x y) (pair_double_coset_finite_support w …`. Introduce `x x' y y' hx hx' hy hy'`. Use extensionality with `v`.

Rewrite using `[Module.End.mul_apply, hkW_apply, hkW_apply, hkW_apply]`. Apply the tactic sequence `exact GlobalTheory.T.finite_support_convolution_triple _ _ _ ρ (iwGL a w) (iwGL b w) (dcos a w (tdiag ϖ x)) (dcos a w (tdiag ϖ x')) (dcos a w (tdiag ϖ (x + x'))) (dcos b w (tdiag ϖ y)) (dcos b w (tdiag ϖ y')) (dcos b w (tdiag ϖ (y + y'))) (fun f hf => by rcases hf with rfl | rfl …`. Establish `hcomm : ∀ i i' : {p : (Fin a → ℤ) × (Fin b → ℤ) // Gap p.1 ∧ Gap p.2}, Commute (hkW ρ (I2 a b w) (dc2 w ϖ i.1.1 i.1.2) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _)) (hkW ρ (I2 a b w) (dc2 w ϖ i'.1.1 i'.1.2) (pair_double_coset_finite_support …`. Introduce `i i'`. Unfold `Commute SemiconjBy`.

Rewrite using `[← hmul _ _ _ _ i.2.1 i'.2.1 i.2.2 i'.2.2, ← hmul _ _ _ _ i'.2.1 i.2.1 i'.2.2 i.2.2, add_comm i.1.1 i'.1.1, add_comm i.1.2 i'.1.2]`. Establish `hT : ∀ v : GlobalTheory.PRep.fixed ρ (I2 a b w), ∑ᶠ q : (GLw a w × GLw b w) ⧸ I2 a b w, u q.out • ρ q.out (v : V) = (((∑ j, c j • hkW ρ (I2 a b w) (dc2 w ϖ (x j) (y j)) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _)) v : GlobalTheory.PRep.fixe …`. Introduce `v`. Rewrite using `[LinearMap.sum_apply, Submodule.coe_sum]`. Simplify using `only [LinearMap.smul_apply, Submodule.coe_smul, hkW_apply, hu]`.

Conclude with `GlobalTheory.CompanionTheory.HeckeSum.finsum_coset_smul_linear _ _ ρ (I2 a b w) J c (fun j => dc2 w ϖ (x j) (y j)) (fun j => pair_double_coset_finite_support w ϖ _ _) v`. Establish `hiter : ∀ (r : ℕ) (v : V) (hv : v ∈ GlobalTheory.PRep.fixed ρ (I2 a b w)), (fun v => κ • ∑ᶠ q : (GLw a w × GLw b w) ⧸ I2 a b w, u q.out • ρ q.out v)^[r] v = ((((κ • ∑ j, c j • hkW ρ (I2 a b w) (dc2 w ϖ (x j) (y j)) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_ …`. Introduce `r`. Proceed by induction on `r with`. Consider the case `zero => intro v hv`.

Both sides reduce to the same expression. Consider the case `succ r ih`. Introduce `v hv`. Rewrite using `[Function.iterate_succ_apply', ih v hv, hT, pow_succ', Module.End.mul_apply, LinearMap.smul_apply, Submodule.coe_smul]`. Establish `hTm : ((∑ j, c j • hkW ρ (I2 a b w) (dc2 w ϖ (x j) (y j)) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _)) ^ m) ⟨v0, hv0⟩ ≠ 0`.

Introduce `h0`. Apply `hne` to reduce the goal to its premises. Rewrite using `[hiter m _ hv0, smul_pow, LinearMap.smul_apply, h0, smul_zero, Submodule.coe_zero]`. Take `⟨v₀, hv₀, χ, hχ, hsum⟩` from `GlobalTheory.T.exists_joint_eigenvector_nonzero (GlobalTheory.PRep.fixed ρ (I2 a b w)) {p : (Fin a → ℤ) × (Fin b → ℤ) // Gap p.1 ∧ Gap p.2} J (fun p => hkW ρ (I2 a b w) (dc2 w ϖ p.1.1 p.1.2) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _)) hcom …`. Establish `hχ2 : ∀ (x : Fin a → ℤ) (y : Fin b → ℤ) (h : Gap x ∧ Gap y), hkW ρ (I2 a b w) (dc2 w ϖ x y) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _) v₀ = χ ⟨(x, y), h⟩ • v₀` using `fun x y h => hχ ⟨(x, y), h⟩`.

Take `⟨χ', hχ'⟩ : ∃ χ' : (Fin a → ℤ) → (Fin b → ℤ) → ℂ, χ' = fun x y => if h : Gap x ∧ Gap y then χ ⟨(x, y), h⟩ else 0` from `⟨_, rfl⟩`. Establish `hχ'mul : ∀ x x' y y', Gap x → Gap x' → Gap y → Gap y' → χ' (x + x') (y + y') = χ' x y * χ' x' y'`. Introduce `x x' y y' hx hx' hy hy'`. Establish `e` using `congrArg (fun T => T v₀) (hmul x x' y y' hx hx' hy hy')`. Simplify using `only [Module.End.mul_apply] at e`.

Rewrite `e` using `[hχ2 _ _ ⟨gap_add hx hx', gap_add hy hy'⟩, hχ2 x' y' ⟨hx', hy'⟩, map_smul, hχ2 x y ⟨hx, hy⟩, smul_smul]`. Establish `e2` using `smul_left_injective ℂ hv₀ e`. Simplify using `only [hχ']`. Rewrite using `[dif_pos ⟨gap_add hx hx', gap_add hy hy'⟩, dif_pos ⟨hx, hy⟩, dif_pos ⟨hx', hy'⟩]`. Rewrite using `[e2, mul_comm]`.

Take `⟨j0, -, hj0⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hsum`. Establish `hex : ∃ x y, Gap x ∧ Gap y ∧ χ' x y ≠ 0`. Use `⟨x j0, y j0, (hgap j0).1, (hgap j0).2, ?_⟩` and prove the remaining obligations. Simplify using `only [hχ']`. Rewrite using `[dif_pos (hgap j0)]`.

Conclude with `right_ne_zero_of_mul hj0`. Take `⟨ξa, ξb, hξ⟩` from `GlobalTheory.T.multiplicative_character_on_cone a b (qh w) (qh_ne w) χ' hχ'mul hex`. Establish `hev : ∀ x y (h : Gap x ∧ Gap y), ev2 w ξa ξb x y = χ ⟨(x, y), h⟩`. Introduce `x y h`. Use `hξ x y h.1 h.2` as an intermediate fact.

Simplify using `only [hχ'] at this`. Rewrite `this` using `[dif_pos h]`. Conclude with `this.symm`. Use `⟨ξa, ξb, ⟨(v₀ : V), v₀.2, by simpa using hv₀, fun x y hx hy => ?_⟩, ?_⟩` and prove the remaining obligations. Establish `e1 : hkG ρ (I2 a b w) (dc2 w ϖ x y) (v₀ : V) = ((hkW ρ (I2 a b w) (dc2 w ϖ x y) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _) v₀ : GlobalTheory.PRep.fixed ρ (I2 a b w)) : V)` using `(hkW_apply _ _ _ _ _ _).symm`.

Rewrite using `[e1, hχ2 x y ⟨hx, hy⟩, Submodule.coe_smul, hev x y ⟨hx, hy⟩]`. Simplify using `only [hev _ _ (hgap _)]`. Conclude with `hsum`.
-/
theorem core (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (hϖ : ordL (ϖ : w.adicCompletion E) = 1)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLw a w × GLw b w) V)
    [FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ (I2 a b w))]
    (J : Type) [Fintype J] (c : J → ℂ) (x : J → Fin a → ℤ) (y : J → Fin b → ℤ)
    (hgap : ∀ j, Gap (x j) ∧ Gap (y j)) (m : ℕ)
    (hm : Module.finrank ℂ (GlobalTheory.PRep.fixed ρ (I2 a b w)) ≤ m) (κ : ℂ) (u : GLw a w × GLw b w → ℂ)
    (hu : u = fun g => ∑ j, c j * dc2 w ϖ (x j) (y j) g) (v0 : V)
    (hv0 : v0 ∈ GlobalTheory.PRep.fixed ρ (I2 a b w))
    (hne : (fun v => κ • ∑ᶠ q : (GLw a w × GLw b w) ⧸ I2 a b w, u q.out • ρ q.out v)^[m] v0 ≠ 0) :
    ∃ (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ), (∃ v ∈ GlobalTheory.PRep.fixed ρ (I2 a b w), v ≠ 0 ∧
      ∀ x y, Gap x → Gap y → hkG ρ (I2 a b w) (dc2 w ϖ x y) v = ev2 w ξa ξb x y • v) ∧
      ∑ j, c j * ev2 w ξa ξb (x j) (y j) ≠ 0 := by
  have hIa := GlobalTheory.T.iwahori_double_coset_finite E w a
  have hIb := GlobalTheory.T.iwahori_double_coset_finite E w b
  have hmul : ∀ (x x' : Fin a → ℤ) (y y' : Fin b → ℤ), Gap x → Gap x' → Gap y → Gap y' →
      hkW ρ (I2 a b w) (dc2 w ϖ (x + x') (y + y')) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _) =
        hkW ρ (I2 a b w) (dc2 w ϖ x y) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _) *
          hkW ρ (I2 a b w) (dc2 w ϖ x' y') (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _) := by
    intro x x' y y' hx hx' hy hy'
    ext v
    rw [Module.End.mul_apply, hkW_apply, hkW_apply, hkW_apply]
    exact GlobalTheory.T.finite_support_convolution_triple _ _ _ ρ (iwGL a w) (iwGL b w) (dcos a w (tdiag ϖ x)) (dcos a w (tdiag ϖ x'))
      (dcos a w (tdiag ϖ (x + x'))) (dcos b w (tdiag ϖ y)) (dcos b w (tdiag ϖ y'))
      (dcos b w (tdiag ϖ (y + y')))
      (fun f hf => by rcases hf with rfl | rfl | rfl <;> exact ⟨(hIa _).1, dcos_inv a w _⟩)
      (fun f hf => by rcases hf with rfl | rfl | rfl <;> exact ⟨(hIb _).1, dcos_inv b w _⟩)
      (fun v hv => GlobalTheory.T.iwahori_hecke_sum_additive E w a ϖ hϖ x x' (gap_anti hx) (gap_anti hx') _
        (ρ.comp (MonoidHom.inl _ _)) v hv)
      (fun v hv => GlobalTheory.T.iwahori_hecke_sum_additive E w b ϖ hϖ y y' (gap_anti hy) (gap_anti hy') _
        (ρ.comp (MonoidHom.inr _ _)) v hv)
      v ((mem_fixed_iff' _ _ _).1 v.2)
  have hcomm : ∀ i i' : {p : (Fin a → ℤ) × (Fin b → ℤ) // Gap p.1 ∧ Gap p.2},
      Commute (hkW ρ (I2 a b w) (dc2 w ϖ i.1.1 i.1.2) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _))
        (hkW ρ (I2 a b w) (dc2 w ϖ i'.1.1 i'.1.2) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _)) := by
    intro i i'
    unfold Commute SemiconjBy
    rw [← hmul _ _ _ _ i.2.1 i'.2.1 i.2.2 i'.2.2, ← hmul _ _ _ _ i'.2.1 i.2.1 i'.2.2 i.2.2,
      add_comm i.1.1 i'.1.1, add_comm i.1.2 i'.1.2]
  have hT : ∀ v : GlobalTheory.PRep.fixed ρ (I2 a b w),
      ∑ᶠ q : (GLw a w × GLw b w) ⧸ I2 a b w, u q.out • ρ q.out (v : V) =
        (((∑ j, c j • hkW ρ (I2 a b w) (dc2 w ϖ (x j) (y j)) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _)) v :
          GlobalTheory.PRep.fixed ρ (I2 a b w)) : V) := by
    intro v
    rw [LinearMap.sum_apply, Submodule.coe_sum]
    simp only [LinearMap.smul_apply, Submodule.coe_smul, hkW_apply, hu]
    exact GlobalTheory.CompanionTheory.HeckeSum.finsum_coset_smul_linear _ _ ρ (I2 a b w) J c (fun j => dc2 w ϖ (x j) (y j))
      (fun j => pair_double_coset_finite_support w ϖ _ _) v
  have hiter : ∀ (r : ℕ) (v : V) (hv : v ∈ GlobalTheory.PRep.fixed ρ (I2 a b w)),
      (fun v => κ • ∑ᶠ q : (GLw a w × GLw b w) ⧸ I2 a b w, u q.out • ρ q.out v)^[r] v =
        ((((κ • ∑ j, c j • hkW ρ (I2 a b w) (dc2 w ϖ (x j) (y j)) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _)) ^ r)
          ⟨v, hv⟩ : GlobalTheory.PRep.fixed ρ (I2 a b w)) : V) := by
    intro r
    induction r with
    | zero => intro v hv; rfl
    | succ r ih =>
      intro v hv
      rw [Function.iterate_succ_apply', ih v hv, hT, pow_succ', Module.End.mul_apply, LinearMap.smul_apply,
        Submodule.coe_smul]
  have hTm : ((∑ j, c j • hkW ρ (I2 a b w) (dc2 w ϖ (x j) (y j)) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _)) ^ m)
      ⟨v0, hv0⟩ ≠ 0 := by
    intro h0
    apply hne
    rw [hiter m _ hv0, smul_pow, LinearMap.smul_apply, h0, smul_zero, Submodule.coe_zero]
  obtain ⟨v₀, hv₀, χ, hχ, hsum⟩ := GlobalTheory.T.exists_joint_eigenvector_nonzero (GlobalTheory.PRep.fixed ρ (I2 a b w))
    {p : (Fin a → ℤ) × (Fin b → ℤ) // Gap p.1 ∧ Gap p.2} J
    (fun p => hkW ρ (I2 a b w) (dc2 w ϖ p.1.1 p.1.2) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _)) hcomm c
    (fun j => ⟨(x j, y j), hgap j⟩) ⟨v0, hv0⟩ m hm hTm
  have hχ2 : ∀ (x : Fin a → ℤ) (y : Fin b → ℤ) (h : Gap x ∧ Gap y),
      hkW ρ (I2 a b w) (dc2 w ϖ x y) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _) v₀ = χ ⟨(x, y), h⟩ • v₀ :=
    fun x y h => hχ ⟨(x, y), h⟩
  obtain ⟨χ', hχ'⟩ : ∃ χ' : (Fin a → ℤ) → (Fin b → ℤ) → ℂ,
      χ' = fun x y => if h : Gap x ∧ Gap y then χ ⟨(x, y), h⟩ else 0 := ⟨_, rfl⟩
  have hχ'mul : ∀ x x' y y', Gap x → Gap x' → Gap y → Gap y' →
      χ' (x + x') (y + y') = χ' x y * χ' x' y' := by
    intro x x' y y' hx hx' hy hy'
    have e := congrArg (fun T => T v₀) (hmul x x' y y' hx hx' hy hy')
    simp only [Module.End.mul_apply] at e
    rw [hχ2 _ _ ⟨gap_add hx hx', gap_add hy hy'⟩, hχ2 x' y' ⟨hx', hy'⟩, map_smul, hχ2 x y ⟨hx, hy⟩,
      smul_smul] at e
    have e2 := smul_left_injective ℂ hv₀ e
    simp only [hχ']
    rw [dif_pos ⟨gap_add hx hx', gap_add hy hy'⟩, dif_pos ⟨hx, hy⟩, dif_pos ⟨hx', hy'⟩]
    rw [e2, mul_comm]
  obtain ⟨j0, -, hj0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hex : ∃ x y, Gap x ∧ Gap y ∧ χ' x y ≠ 0 := by
    refine ⟨x j0, y j0, (hgap j0).1, (hgap j0).2, ?_⟩
    simp only [hχ']
    rw [dif_pos (hgap j0)]
    exact right_ne_zero_of_mul hj0
  obtain ⟨ξa, ξb, hξ⟩ := GlobalTheory.T.multiplicative_character_on_cone a b (qh w) (qh_ne w) χ' hχ'mul hex
  have hev : ∀ x y (h : Gap x ∧ Gap y), ev2 w ξa ξb x y = χ ⟨(x, y), h⟩ := by
    intro x y h
    have := hξ x y h.1 h.2
    simp only [hχ'] at this
    rw [dif_pos h] at this
    exact this.symm
  refine ⟨ξa, ξb, ⟨(v₀ : V), v₀.2, by simpa using hv₀, fun x y hx hy => ?_⟩, ?_⟩
  · have e1 : hkG ρ (I2 a b w) (dc2 w ϖ x y) (v₀ : V) =
        ((hkW ρ (I2 a b w) (dc2 w ϖ x y) (pair_double_coset_finite_support w ϖ _ _) (pair_double_coset_bi_invariant w ϖ _ _) v₀ :
          GlobalTheory.PRep.fixed ρ (I2 a b w)) : V) :=
      (hkW_apply _ _ _ _ _ _).symm
    rw [e1, hχ2 x y ⟨hx, hy⟩, Submodule.coe_smul, hev x y ⟨hx, hy⟩]
  · simp only [hev _ _ (hgap _)]
    exact hsum

end Place

set_option maxHeartbeats 1600000 in
/- English proof (translation)
Introduce `hRM E _ _ _ n a b μ s₁ s₂ Pa Pb D hC w ϖ J _ c x y m G hϖ hgap hm hGS hGI hne`. Take `⟨hinv, J', L, hLeq, hLsep⟩` from `hRM E a b s₁ s₂ Pa Pb w hC.g₁ hC.g₂ hC.u₁ hC.u₂ hC.t₁ hC.t₂`. Establish `hIa` using `GlobalTheory.T.iwahori_double_coset_finite E w a`. Establish `hIb` using `GlobalTheory.T.iwahori_double_coset_finite E w b`. Establish `hIopen : IsOpen ((I2 a b w : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w))`.

Rewrite using `[Subgroup.coe_prod]`. Conclude with `(hIa 1).2.1.prod (hIb 1).2.1`. Establish `hK : I2 a b w ≤ K2 a b w` using `Subgroup.prod_mono (hIa 1).2.2.2.1 (hIb 1).2.2.2.1`. Establish `hidx : (I2 a b w).relIndex (K2 a b w) ≠ 0` using `GlobalTheory.T.prod_rel_index_ne_zero _ _ _ _ _ _ (hIa 1).2.2.2.2 (hIb 1).2.2.2.2`. Take `⟨u, hu⟩ : ∃ u : GLw a w × GLw b w → ℂ, u = fun g => ∑ j, c j * dc2 w ϖ (x j) (y j) g` from `⟨_, rfl⟩`.

Rewrite `hne` using `[← hu]`. Establish `hufin : (Function.support fun q : (GLw a w × GLw b w) ⧸ I2 a b w => u q.out).Finite`. Use `(Set.finite_iUnion fun j => pair_double_coset_finite_support w ϖ (x j) (y j)).subset ?_` and prove the remaining obligations. Introduce `q hq`. Assume the negation of the conclusion as `hcon`.

Apply `hq` to reduce the goal to its premises. Simplify using `only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hcon`. Simplify using `[hu, hcon]`. Establish `hubi : ∀ k ∈ I2 a b w, ∀ g, u (k * g) = u g ∧ u (g * k) = u g`. Introduce `k hk g`.

Simplify using `only [hu, (pair_double_coset_bi_invariant w ϖ _ _ k hk g).1, (pair_double_coset_bi_invariant w ϖ _ _ k hk g).2, and_self]`. Take `⟨κ, hκ⟩ : ∃ κ : ℂ, κ = (((I2 a b w).relIndex (K2 a b w) : ℕ) : ℂ)⁻¹` from `⟨_, rfl⟩`. Establish `hact : ∀ F : H E a b → ℂ, (∀ k ∈ I2 a b w, pairRt a b w k F = F) → actP w u F = κ • ∑ᶠ q : (GLw a w × GLw b w) ⧸ I2 a b w, u q.out • pairRt a b w q.out F`. Introduce `F hF`. Use function extensionality and compare the values at `z`.

Establish `hr : ∀ l ∈ I2 a b w, ∀ g : GLw a w × GLw b w, (fun m => u m * pairRt a b w m F z) (g * l) = (fun m => u m * pairRt a b w m F z) g`. Introduce `l hl g`. Use `show u (g * l) * pairRt a b w (g * l) F z = u g * pairRt a b w g F z`. Rewrite using `[(hubi l hl g).2, map_mul, Module.End.mul_apply, hF l hl]`. Establish `hsub : (Function.support fun q : (GLw a w × GLw b w) ⧸ I2 a b w => u q.out * pairRt a b w q.out F z) ⊆ hufin.toFinset`.

Introduce `q hq`. Rewrite using `[Set.Finite.coe_toFinset]`. Introduce `h0`. Apply `hq` to reduce the goal to its premises. Simplify using `[h0]`.

Use `show hint (K2 a b w) (fun m => u m * pairRt a b w m F z) = _`. Rewrite using `[GlobalTheory.T.hecke_integral_finite_sum _ (K2 a b w) (I2 a b w) (fun m => u m * pairRt a b w m F z) hK hidx hr, ← hκ, finsum_eq_sum_of_support_subset _ hsub, hsum_eq (pairRt a b w) (I2 a b w) u hufin.coe_toFinset.ge F]`. Simplify using `only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]`. Establish `hGI' : ∀ k ∈ I2 a b w, pairRt a b w k G = G` using `(mem_fixed_iff' _ _ _).1 hGI`. Take `⟨hmS, hmI, -⟩` from `iter_push (pairRt a b w) (pairSpace s₁.space s₂.space) (pairAt Pa Pb w) 0 hinv (fun _ _ _ _ => by simp) (I2 a b w) hIopen u hufin hubi κ (actP w u) hact G hGS hGI' m`.

Choose the witnesses or unpack the hypotheses as in `⟨j', hj'⟩ : ∃ j', L j' ((actP w u)^[m] G) ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `hne (hLsep _ hmS ⟨I2 a b w, hIopen, (mem_fixed_iff' _ _ _).2 hmI⟩ hcon)`. Take `⟨-, -, hLm⟩` from `iter_push (pairRt a b w) (pairSpace s₁.space s₂.space) (pairAt Pa Pb w) (L j') hinv (hLeq j') (I2 a b w) hIopen u hufin hubi κ (actP w u) hact G hGS hGI' m`.

Establish `hsmG : SmVec (pairRt a b w) G` using `⟨I2 a b w, hIopen, hGI⟩`. Establish `hv0 : L j' G ∈ GlobalTheory.PRep.fixed (pairAt Pa Pb w) (I2 a b w)` using `(mem_fixed_iff' _ _ _).2 fun k hk => (hLeq j' k G hGS hsmG).symm.trans (congrArg (L j') (hGI' k hk))`. Use `haveI hfd : FiniteDimensional ℂ (GlobalTheory.PRep.fixed (pairAt Pa Pb w) (I2 a b w)) := GlobalTheory.T.finiteDimensional_fixed_tensor _ _ _ _ (lp Pa w) (lp Pb w) (iwGL a w) (iwGL b w) ((GlobalTheory.T.admissible_parabolic_induction (w.adicCompletion E) _ Pa.h (fun i => Pa.σ i w) …`. Conclude with `core w ϖ hϖ (pairAt Pa Pb w) J c x y hgap m hm κ u hu (L j' G) hv0 fun h => hj' (hLm.trans h)`.
-/
theorem rReadT : RReadT := by
  intro hRM E _ _ _ n a b μ s₁ s₂ Pa Pb D hC w ϖ J _ c x y m G hϖ hgap hm hGS hGI hne
  obtain ⟨hinv, J', L, hLeq, hLsep⟩ := hRM E a b s₁ s₂ Pa Pb w hC.g₁ hC.g₂ hC.u₁ hC.u₂ hC.t₁ hC.t₂
  have hIa := GlobalTheory.T.iwahori_double_coset_finite E w a
  have hIb := GlobalTheory.T.iwahori_double_coset_finite E w b
  have hIopen : IsOpen ((I2 a b w : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_prod]
    exact (hIa 1).2.1.prod (hIb 1).2.1
  have hK : I2 a b w ≤ K2 a b w := Subgroup.prod_mono (hIa 1).2.2.2.1 (hIb 1).2.2.2.1
  have hidx : (I2 a b w).relIndex (K2 a b w) ≠ 0 :=
    GlobalTheory.T.prod_rel_index_ne_zero _ _ _ _ _ _ (hIa 1).2.2.2.2 (hIb 1).2.2.2.2
  obtain ⟨u, hu⟩ : ∃ u : GLw a w × GLw b w → ℂ, u = fun g => ∑ j, c j * dc2 w ϖ (x j) (y j) g := ⟨_, rfl⟩
  rw [← hu] at hne
  have hufin : (Function.support fun q : (GLw a w × GLw b w) ⧸ I2 a b w => u q.out).Finite := by
    refine (Set.finite_iUnion fun j => pair_double_coset_finite_support w ϖ (x j) (y j)).subset ?_
    intro q hq
    by_contra hcon
    apply hq
    simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hcon
    simp [hu, hcon]
  have hubi : ∀ k ∈ I2 a b w, ∀ g, u (k * g) = u g ∧ u (g * k) = u g := by
    intro k hk g
    simp only [hu, (pair_double_coset_bi_invariant w ϖ _ _ k hk g).1, (pair_double_coset_bi_invariant w ϖ _ _ k hk g).2, and_self]
  obtain ⟨κ, hκ⟩ : ∃ κ : ℂ, κ = (((I2 a b w).relIndex (K2 a b w) : ℕ) : ℂ)⁻¹ := ⟨_, rfl⟩
  have hact : ∀ F : H E a b → ℂ, (∀ k ∈ I2 a b w, pairRt a b w k F = F) →
      actP w u F = κ • ∑ᶠ q : (GLw a w × GLw b w) ⧸ I2 a b w, u q.out • pairRt a b w q.out F := by
    intro F hF
    funext z
    have hr : ∀ l ∈ I2 a b w, ∀ g : GLw a w × GLw b w,
        (fun m => u m * pairRt a b w m F z) (g * l) = (fun m => u m * pairRt a b w m F z) g := by
      intro l hl g
      show u (g * l) * pairRt a b w (g * l) F z = u g * pairRt a b w g F z
      rw [(hubi l hl g).2, map_mul, Module.End.mul_apply, hF l hl]
    have hsub : (Function.support fun q : (GLw a w × GLw b w) ⧸ I2 a b w =>
        u q.out * pairRt a b w q.out F z) ⊆ hufin.toFinset := by
      intro q hq
      rw [Set.Finite.coe_toFinset]
      intro h0
      apply hq
      simp [h0]
    show hint (K2 a b w) (fun m => u m * pairRt a b w m F z) = _
    rw [GlobalTheory.T.hecke_integral_finite_sum _ (K2 a b w) (I2 a b w) (fun m => u m * pairRt a b w m F z) hK hidx hr, ← hκ,
      finsum_eq_sum_of_support_subset _ hsub, hsum_eq (pairRt a b w) (I2 a b w) u hufin.coe_toFinset.ge F]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  have hGI' : ∀ k ∈ I2 a b w, pairRt a b w k G = G := (mem_fixed_iff' _ _ _).1 hGI
  obtain ⟨hmS, hmI, -⟩ := iter_push (pairRt a b w) (pairSpace s₁.space s₂.space) (pairAt Pa Pb w) 0 hinv
    (fun _ _ _ _ => by simp) (I2 a b w) hIopen u hufin hubi κ (actP w u) hact G hGS hGI' m
  obtain ⟨j', hj'⟩ : ∃ j', L j' ((actP w u)^[m] G) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (hLsep _ hmS ⟨I2 a b w, hIopen, (mem_fixed_iff' _ _ _).2 hmI⟩ hcon)
  obtain ⟨-, -, hLm⟩ := iter_push (pairRt a b w) (pairSpace s₁.space s₂.space) (pairAt Pa Pb w) (L j') hinv
    (hLeq j') (I2 a b w) hIopen u hufin hubi κ (actP w u) hact G hGS hGI' m
  have hsmG : SmVec (pairRt a b w) G := ⟨I2 a b w, hIopen, hGI⟩
  have hv0 : L j' G ∈ GlobalTheory.PRep.fixed (pairAt Pa Pb w) (I2 a b w) :=
    (mem_fixed_iff' _ _ _).2 fun k hk => (hLeq j' k G hGS hsmG).symm.trans (congrArg (L j') (hGI' k hk))
  haveI hfd : FiniteDimensional ℂ (GlobalTheory.PRep.fixed (pairAt Pa Pb w) (I2 a b w)) :=
    GlobalTheory.T.finiteDimensional_fixed_tensor _ _ _ _ (lp Pa w) (lp Pb w) (iwGL a w) (iwGL b w)
      ((GlobalTheory.T.admissible_parabolic_induction (w.adicCompletion E) _ Pa.h (fun i => Pa.σ i w)).2 _ (hIa 1).2.1 (hIa 1).2.2.1)
      ((GlobalTheory.T.admissible_parabolic_induction (w.adicCompletion E) _ Pb.h (fun i => Pb.σ i w)).2 _ (hIb 1).2.1 (hIb 1).2.2.1)
  exact core w ϖ hϖ (pairAt Pa Pb w) J c x y hgap m hm κ u hu (L j' G) hv0 fun h => hj' (hLm.trans h)

end PositivityTheory.Rg.BcB.F.Tail

end
