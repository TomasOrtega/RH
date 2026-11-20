import Mathlib
import Formalism.GL3MeanSquares.HookFormulaTorsion.DoubleCosetDecompositionAll
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemFormsIffExistsEquivariantExtensionStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimeIncidenceFiniteFibresStableStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UopIsExtStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainTransitionIsExtKernelSumStatement
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

noncomputable section

namespace GlobalTheory.LvT

/- English proof (translation)
Use `letI : Module ℚ V := Module.compHom V (algebraMap ℚ ℂ)`. Establish `hfin' : ∀ p : P, Finite (MulAction.stabilizer G p)`. Introduce `p`. Take `⟨c, g, rfl⟩` from `hsurj p`. Use `haveI := hfin c`.

Conclude with `Finite.of_equiv _ (MulAction.stabilizerEquivStabilizer (a := rep c) (g := g) rfl).toEquiv`. Establish `hR : ∀ a : P, ∃! r, r ∈ Finset.univ.image rep ∧ r ∈ MulAction.orbit G a`. Introduce `a`. Take `⟨c, g, rfl⟩` from `hsurj a`. Use `⟨rep c, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), g⁻¹, inv_smul_smul g _⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `r ⟨hr, γ, hγ⟩`. Take `⟨c', -, rfl⟩` from `Finset.mem_image.mp hr`. Establish `: c = c'` using `hinj c c' (γ * g) (by rw [mul_smul]; exact hγ)`. Rewrite using `[this]`. Establish `hrinj : Function.Injective rep` using `fun c c' h => hinj c c' 1 (by rw [one_smul, h])`.

Establish `key` using `Formalism.HermitianLattices.RamifiedLatticeOperators.count_of_orbits G P P V (fun a => (hup a).toFinset) (fun b => (hdn b).toFinset) F (Finset.univ.image rep) (Finset.univ.image rep) (by intro a b; simp) (by intro γ a b h; simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at …`. Rewrite `key` using `[Finset.sum_image (fun a _ b _ h => hrinj h), Finset.sum_image (fun a _ b _ h => hrinj h)]`. Establish `hq : ∀ (n : ℕ) (x : V), ((n : ℚ))⁻¹ • x = ((n : ℂ))⁻¹ • x`. Introduce `n x`. Express the relevant statement in the definitionally equal form `(algebraMap ℚ ℂ ((n : ℚ))⁻¹) • x = _`.

Simplify using the standard rewrite rules. Simplify using `only [hq] at key`. Simplify using `only [finsum_mem_eq_finite_toFinset_sum _ (hup _), finsum_mem_eq_finite_toFinset_sum _ (hdn _)]`. Conclude with `key`.
-/
theorem count_incidence {G P C V : Type} [Group G] [MulAction G P] [Fintype C] [AddCommGroup V] [Module ℂ V]
    (rep : C → P) (hsurj : ∀ p, ∃ (c : C) (g : G), g • rep c = p)
    (hinj : ∀ (c c' : C) (g : G), g • rep c = rep c' → c = c')
    (hfin : ∀ c, Finite (MulAction.stabilizer G (rep c)))
    (I : P → P → Prop) (hup : ∀ p, {q | I p q}.Finite) (hdn : ∀ p, {q | I q p}.Finite)
    (hI : ∀ (g : G) p q, I p q → I (g • p) (g • q))
    (F : P → P → V) (hF : ∀ (g : G) p q, F (g • p) (g • q) = F p q) :
    ∑ c, ((Nat.card (MulAction.stabilizer G (rep c)) : ℂ))⁻¹ • ∑ᶠ q ∈ {q | I (rep c) q}, F (rep c) q =
      ∑ c, ((Nat.card (MulAction.stabilizer G (rep c)) : ℂ))⁻¹ • ∑ᶠ p ∈ {p | I p (rep c)}, F p (rep c) := by
  letI : Module ℚ V := Module.compHom V (algebraMap ℚ ℂ)
  have hfin' : ∀ p : P, Finite (MulAction.stabilizer G p) := by
    intro p
    obtain ⟨c, g, rfl⟩ := hsurj p
    haveI := hfin c
    exact Finite.of_equiv _ (MulAction.stabilizerEquivStabilizer (a := rep c) (g := g) rfl).toEquiv
  have hR : ∀ a : P, ∃! r, r ∈ Finset.univ.image rep ∧ r ∈ MulAction.orbit G a := by
    intro a
    obtain ⟨c, g, rfl⟩ := hsurj a
    refine ⟨rep c, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), g⁻¹, inv_smul_smul g _⟩, ?_⟩
    rintro r ⟨hr, γ, hγ⟩
    obtain ⟨c', -, rfl⟩ := Finset.mem_image.mp hr
    have : c = c' := hinj c c' (γ * g) (by rw [mul_smul]; exact hγ)
    rw [this]
  have hrinj : Function.Injective rep := fun c c' h => hinj c c' 1 (by rw [one_smul, h])
  have key := Formalism.HermitianLattices.RamifiedLatticeOperators.count_of_orbits G P P V (fun a => (hup a).toFinset) (fun b => (hdn b).toFinset) F
    (Finset.univ.image rep) (Finset.univ.image rep) (by intro a b; simp)
    (by intro γ a b h; simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h ⊢; exact hI γ a b h)
    (fun γ a b _ => hF γ a b) hfin' hfin' hR hR
  rw [Finset.sum_image (fun a _ b _ h => hrinj h), Finset.sum_image (fun a _ b _ h => hrinj h)] at key
  have hq : ∀ (n : ℕ) (x : V), ((n : ℚ))⁻¹ • x = ((n : ℂ))⁻¹ • x := by
    intro n x
    change (algebraMap ℚ ℂ ((n : ℚ))⁻¹) • x = _
    simp
  simp only [hq] at key
  simp only [finsum_mem_eq_finite_toFinset_sum _ (hup _), finsum_mem_eq_finite_toFinset_sum _ (hdn _)]
  exact key

/- English proof (translation)
Introduce `D u X Lv Kt htgt huk i hi v φ hφ`. Use `set M := Lv i hi.le with hM`. Use `set M' := Lv (i + 1) hi with hM'`. Set `K : KerPt M M'` to `Kt i hi`. Establish `hT : K.TgtEq` using `htgt i hi`.

Establish `hU : K.UKLaw` using `huk i hi`. Take `⟨Φ, hΦ⟩` from `(GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i M φ).1 hφ`. Take `⟨hfinI, hstab, -⟩` from `GlobalTheory.T.levelPrime_incidence_finite_fibres_stable D u X i M v`. Take `⟨hfinI', -, -⟩` from `GlobalTheory.T.levelPrime_incidence_finite_fibres_stable D u X (i + 1) M' v`. Establish `h1` using `GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X (i + 1) M' v _ _ (GlobalTheory.T.levelChainTransition_isExt_kernel_sum D u X i M M' K φ Φ hT hΦ)`.

Establish `h2` using `GlobalTheory.T.levelChainTransition_isExt_kernel_sum D u X i M M' K _ _ hT (GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i M v φ Φ hΦ)`. Establish `hpow : ((((X.A.T : ℝ) ^ (((D.R.t : ℝ) + 1) / 2) : ℝ)) : ℂ) = (X.A.T : ℂ) ^ ((D.R.t + 1) / 2)`. Take `⟨k, hk⟩` from `D.R.t_odd`. Establish `e1 : (D.R.t + 1) / 2 = k + 1` using `by omega`. Establish `e2 : ((D.R.t : ℝ) + 1) / 2 = ((k + 1 : ℕ) : ℝ)` using `by rw [hk]; push_cast; ring`.

Rewrite using `[e1, e2, Real.rpow_natCast]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hwt : ∀ c, X.C.wt i c = ((Nat.card (MulAction.stabilizer M.G (M.rep c)) : ℂ))⁻¹`. Introduce `c`.

Rewrite using `[← M.card_stab]`. Both sides reduce to the same expression. Establish `hfs : ∀ c, Finite (MulAction.stabilizer M.G (M.rep c))`. Introduce `c`. Apply `Nat.finite_of_card_ne_zero` to reduce the goal to its premises.

Rewrite using `[← M.card_stab]`. Use `haveI := X.C.stabFin i c`. Use `letI := X.C.stabGrp i c`. Conclude with `Nat.card_pos.ne'`. Use function extensionality and compare the values at `c'`.

Rewrite using `[hpow, Pi.smul_apply, h1.1 c', h2.1 c', ← Submodule.coe_smul]`. Use `congr 1`. Establish `key` using `count_incidence M.rep M.rep_surj M.rep_inj hfs (M.Inc v) (fun p => (hfinI p).1) (fun p => (hfinI p).2) (fun g p q h => (hstab g p q).1 h) (fun p q => K.k p (M'.rep c') (Φ q)) (fun g p q => by rw [hΦ.2, K.src])`. Establish `hL : ∀ c, K.k (M.rep c) (M'.rep c') (∑ᶠ p₁ ∈ {p₁ | M.Inc v (M.rep c) p₁}, Φ p₁) = ∑ᶠ p₁ ∈ {p₁ | M.Inc v (M.rep c) p₁}, K.k (M.rep c) (M'.rep c') (Φ p₁)`. Introduce `c`.

Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ (hfinI _).1, finsum_mem_eq_finite_toFinset_sum _ (hfinI _).1, map_sum]`. Simplify using `only [hL, hwt]`. Rewrite using `[key, finsum_mem_eq_finite_toFinset_sum _ (hfinI' _).1, Finset.sum_comm, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.smul_sum, smul_comm, ← hU v, finsum_mem_eq_finite_toFinset_sum _ (hfinI' _).1]`.
-/
theorem levelChainUOperatorCommutation_of_pointPairLaw : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (Lv : LevTie X) (Kt : KerTie Lv),
    (∀ i h, (Kt i h).TgtEq) → (∀ i h, (Kt i h).UKLaw) → LevelChainUOperatorCommutation X := by
  intro D u X Lv Kt htgt huk i hi v φ hφ
  set M := Lv i hi.le with hM
  set M' := Lv (i + 1) hi with hM'
  let K : KerPt M M' := Kt i hi
  have hT : K.TgtEq := htgt i hi
  have hU : K.UKLaw := huk i hi
  obtain ⟨Φ, hΦ⟩ := (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i M φ).1 hφ
  obtain ⟨hfinI, hstab, -⟩ := GlobalTheory.T.levelPrime_incidence_finite_fibres_stable D u X i M v
  obtain ⟨hfinI', -, -⟩ := GlobalTheory.T.levelPrime_incidence_finite_fibres_stable D u X (i + 1) M' v
  have h1 := GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X (i + 1) M' v _ _ (GlobalTheory.T.levelChainTransition_isExt_kernel_sum D u X i M M' K φ Φ hT hΦ)
  have h2 := GlobalTheory.T.levelChainTransition_isExt_kernel_sum D u X i M M' K _ _ hT (GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i M v φ Φ hΦ)
  have hpow : ((((X.A.T : ℝ) ^ (((D.R.t : ℝ) + 1) / 2) : ℝ)) : ℂ) = (X.A.T : ℂ) ^ ((D.R.t + 1) / 2) := by
    obtain ⟨k, hk⟩ := D.R.t_odd
    have e1 : (D.R.t + 1) / 2 = k + 1 := by omega
    have e2 : ((D.R.t : ℝ) + 1) / 2 = ((k + 1 : ℕ) : ℝ) := by rw [hk]; push_cast; ring
    rw [e1, e2, Real.rpow_natCast]
    push_cast; rfl
  have hwt : ∀ c, X.C.wt i c = ((Nat.card (MulAction.stabilizer M.G (M.rep c)) : ℂ))⁻¹ := by
    intro c
    rw [← M.card_stab]; rfl
  have hfs : ∀ c, Finite (MulAction.stabilizer M.G (M.rep c)) := by
    intro c
    apply Nat.finite_of_card_ne_zero
    rw [← M.card_stab]
    haveI := X.C.stabFin i c
    letI := X.C.stabGrp i c
    exact Nat.card_pos.ne'
  funext c'
  rw [hpow, Pi.smul_apply, h1.1 c', h2.1 c', ← Submodule.coe_smul]
  congr 1
  have key := count_incidence M.rep M.rep_surj M.rep_inj hfs (M.Inc v) (fun p => (hfinI p).1) (fun p => (hfinI p).2)
    (fun g p q h => (hstab g p q).1 h) (fun p q => K.k p (M'.rep c') (Φ q))
    (fun g p q => by rw [hΦ.2, K.src])
  have hL : ∀ c, K.k (M.rep c) (M'.rep c') (∑ᶠ p₁ ∈ {p₁ | M.Inc v (M.rep c) p₁}, Φ p₁) =
      ∑ᶠ p₁ ∈ {p₁ | M.Inc v (M.rep c) p₁}, K.k (M.rep c) (M'.rep c') (Φ p₁) := by
    intro c
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfinI _).1, finsum_mem_eq_finite_toFinset_sum _ (hfinI _).1, map_sum]
  simp only [hL, hwt]
  rw [key, finsum_mem_eq_finite_toFinset_sum _ (hfinI' _).1, Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.smul_sum, smul_comm, ← hU v, finsum_mem_eq_finite_toFinset_sum _ (hfinI' _).1]

end GlobalTheory.LvT
