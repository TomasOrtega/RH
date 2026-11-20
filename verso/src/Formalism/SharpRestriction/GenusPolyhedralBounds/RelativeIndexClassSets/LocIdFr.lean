import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.CompletionIntegersIff
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLoc

noncomputable section

namespace Formalism.MainNotions.Gaps.Loc

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨P, hP, hP0⟩` from `RingOfIntegers.isIntegral_coe x`. Establish `h2 : IsIntegral (w.adicCompletionIntegers F) (ρ (x : E))`. Use `⟨P.map (Int.castRingHom _), hP.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map]`. Establish `e : (algebraMap (w.adicCompletionIntegers F) (w.adicCompletion F)).comp (Int.castRingHom _) = ρ.comp (algebraMap ℤ E)` using `RingHom.ext_int _ _`.

Rewrite using `[e, ← Polynomial.hom_eval₂, hP0, map_zero]`. Take `⟨y, hy⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := w.adicCompletionIntegers F) (K := w.adicCompletion F)).1 h2`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem hom_int (w : HeightOneSpectrum (𝓞 F)) (ρ : E →+* w.adicCompletion F) (x : 𝓞 E) :
    ρ (x : E) ∈ w.adicCompletionIntegers F := by
  obtain ⟨P, hP, hP0⟩ := RingOfIntegers.isIntegral_coe x
  have h2 : IsIntegral (w.adicCompletionIntegers F) (ρ (x : E)) := by
    refine ⟨P.map (Int.castRingHom _), hP.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap (w.adicCompletionIntegers F) (w.adicCompletion F)).comp (Int.castRingHom _) =
        ρ.comp (algebraMap ℤ E) := RingHom.ext_int _ _
    rw [e, ← Polynomial.hom_eval₂, hP0, map_zero]
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := w.adicCompletionIntegers F)
    (K := w.adicCompletion F)).1 h2
  rw [← hy]; exact y.2

/- English proof (translation)
Establish `hle : intV E w ≤ (w.adicCompletionIntegers F).toSubring.comap ((RingHom.fst _ _).comp φ.toRingHom)`. Use `Subring.closure_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ (⟨⟨_, ⟨y, rfl⟩⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)`. Conclude with `hom_int w (((RingHom.fst _ _).comp φ.toRingHom).comp (inclE (F := F) (w.adicCompletion F))) y`. Use `show (φ ((1 : E) ⊗ₜ[F] c)).1 ∈ w.adicCompletionIntegers F`.

Rewrite using `[halg]`. Conclude with `hc`. Conclude with `hle hs`.
-/
theorem fst_int (w : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] w.adicCompletion F ≃+* w.adicCompletion F × w.adicCompletion F)
    (halg : ∀ a : w.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = (a, a))
    (s : E ⊗[F] w.adicCompletion F) (hs : s ∈ intV E w) : (φ s).1 ∈ w.adicCompletionIntegers F := by
  have hle : intV E w ≤ (w.adicCompletionIntegers F).toSubring.comap
      ((RingHom.fst _ _).comp φ.toRingHom) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨_, ⟨y, rfl⟩⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
    · exact hom_int w (((RingHom.fst _ _).comp φ.toRingHom).comp (inclE (F := F) (w.adicCompletion F))) y
    · show (φ ((1 : E) ⊗ₜ[F] c)).1 ∈ w.adicCompletionIntegers F
      rw [halg]; exact hc
  exact hle hs

/- English proof (translation)
Take `⟨φ, hφ⟩` from `Formalism.MainNotions.Gaps.LG.sc_exists_iso sig h2 ψ b hb0 hb`. Use `⟨φ, fun x => ?_, fun a => ?_, fun x => ?_⟩` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]`.

Consider the case `tmul x c`. Establish `: sigR sig K (x ⊗ₜ[F] c) = sig x ⊗ₜ[F] c` using `rfl`. Rewrite using `[this, hφ, hφ, hsig]`. Both sides reduce to the same expression. Rewrite using `[hφ]`.

Simplify using the standard rewrite rules. Establish `: inclE (F` using `F) K x = x ⊗ₜ[F] (1 : K) := rfl`. Rewrite using `[this, hφ, one_mul]`.
-/
theorem exists_spl {K : Type} [Field K] [Algebra F K] (sig : E →ₐ[F] E) (hsig : ∀ x, sig (sig x) = x)
    (h2 : Module.finrank F E = 2) (b : E) (hb0 : b ≠ 0) (hb : sig b = -b) (ψ : E →ₐ[F] K) :
    ∃ φ : E ⊗[F] K ≃+* K × K, (∀ x, φ (sigR sig K x) = swapR _ (φ x)) ∧
      (∀ a : K, φ ((1 : E) ⊗ₜ[F] a) = (a, a)) ∧ ∀ x : E, (φ (inclE (F := F) K x)).1 = ψ x := by
  obtain ⟨φ, hφ⟩ := Formalism.MainNotions.Gaps.LG.sc_exists_iso sig h2 ψ b hb0 hb
  refine ⟨φ, fun x => ?_, fun a => ?_, fun x => ?_⟩
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
    | tmul x c =>
      have : sigR sig K (x ⊗ₜ[F] c) = sig x ⊗ₜ[F] c := rfl
      rw [this, hφ, hφ, hsig]; rfl
  · rw [hφ]; simp
  · have : inclE (F := F) K x = x ⊗ₜ[F] (1 : K) := rfl
    rw [this, hφ, one_mul]

/- English proof (translation)
Use `set π : E ⊗[F] w.adicCompletion F →+* w.adicCompletion F := (RingHom.fst _ _).comp φ.toRingHom with hπ`. Use `set ρ : E →+* w.adicCompletion F := π.comp (inclE (F := F) (w.adicCompletion F)) with hρ`. Establish `hπa : ∀ s, π s = (φ s).1` using `fun _ => rfl`. Establish `hinv : (((bc ρ B)⁻¹ : GL (Fin k) (w.adicCompletion F)) : Matrix (Fin k) (Fin k) (w.adicCompletion F)) = ((B⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E).map ρ`. Rewrite using `[← map_inv]`.

Both sides reduce to the same expression. Establish `hval : ((bc ρ B : GL (Fin k) (w.adicCompletion F)) : Matrix (Fin k) (Fin k) (w.adicCompletion F)) = (B : Matrix (Fin k) (Fin k) E).map ρ` using `rfl`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, hxt⟩`. Establish `ht : t = fun a => π (x a)` using `funext fun a => (hxt a).symm`.

Rewrite using `[ht]`. Use `clear ht hxt`. Unfold `Formalism.L2.Herm.locL latS at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨l, hl, rfl⟩` from `hx`. Introduce `a`. Establish `e1 : ((((B⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E).map ρ) *ᵥ (fun b => π (inclE (F` using `F) (w.adicCompletion F) (l b)))) a = ρ ((((B⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ l) a) := (RingHom.map_mulVec ρ _ l a).symm`. Rewrite using `[hinv, e1]`. Take `⟨y, hy⟩` from `h1 l hl a`.

Rewrite using `[← hy]`. Conclude with `hom_int w ρ y`. Consider the case `zero`. Introduce `a`. Establish `: (fun b => π ((0 : Fin k → E ⊗[F] w.adicCompletion F) b)) = 0`.

Use function extensionality and compare the values at `b`. Simplify using the standard rewrite rules. Rewrite using `[this, mulVec_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy`.

Introduce `a`. Establish `: (fun b => π ((x + y) b)) = (fun b => π (x b)) + fun b => π (y b)`. Use function extensionality and compare the values at `b`. Simplify using the standard rewrite rules. Rewrite using `[this, mulVec_add]`.

Conclude with `add_mem (hx a) (hy a)`. Consider the case `smul s x _ hx`. Introduce `a`. Establish `: (fun b => π ((s • x) b)) = π (s : E ⊗[F] w.adicCompletion F) • fun b => π (x b)`. Use function extensionality and compare the values at `b`.

Use `show π ((s : E ⊗[F] w.adicCompletion F) * x b) = π (s : E ⊗[F] w.adicCompletion F) * π (x b)`. Rewrite using `[map_mul]`. Rewrite using `[this, mulVec_smul]`. Conclude with `mul_mem (fst_int w φ halg _ s.2) (hx a)`. Introduce `hu set u : Fin k → w.adicCompletion F := (((bc ρ B)⁻¹ : GL (Fin k) (w.adicCompletion F)) : Matrix (Fin k) (Fin k) (w.adicCompletion F)) *ᵥ t with hudef`.

Establish `ht : t = (B : Matrix (Fin k) (Fin k) E).map ρ *ᵥ u`. Rewrite using `[← hval, hudef, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]`. Establish `hNv : Valued.v ((N : ℕ) : w.adicCompletion F) = 1`. Use `Formalism.MainNotions.Gaps.LG.sc_val_one w (N : 𝓞 F) hN` as an intermediate fact. Simplify using `using this`.

Establish `hN0 : ((N : ℕ) : w.adicCompletion F) ≠ 0`. Introduce `h0`. Rewrite `hNv` using `[h0, map_zero]`. Conclude with `zero_ne_one hNv`. Establish `hNi : ((N : ℕ) : w.adicCompletion F)⁻¹ ∈ w.adicCompletionIntegers F`.

Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hNv, inv_one]`. Set `s : Fin k → intV E w` to `fun i => ⟨(1 : E) ⊗ₜ[F] (u i * ((N : ℕ) : w.adicCompletion F)⁻¹), Formalism.MainNotions.Gaps.LG.sc_right_mem w _ (mul_mem (hu i) hNi)⟩`. Set `g : Fin k → Fin k → E ⊗[F] w.adicCompletion F` to `fun i a => inclE (F := F) (w.adicCompletion F) (((N : E) • ((B : Matrix (Fin k) (Fin k) E) *ᵥ Pi.single i 1)) a)`. Use `⟨∑ i, s i • g i, ?_, fun a => ?_⟩` and prove the remaining obligations. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h2 i, rfl⟩)`.

Establish `hB : ∀ i, ((B : Matrix (Fin k) (Fin k) E) *ᵥ Pi.single i 1) a = (B : Matrix (Fin k) (Fin k) E) a i`. Introduce `i`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Establish `hterm : ∀ i, π ((s i • g i) a) = ρ ((B : Matrix (Fin k) (Fin k) E) a i) * u i`. Introduce `i`.

Use `show π (((1 : E) ⊗ₜ[F] (u i * ((N : ℕ) : w.adicCompletion F)⁻¹)) * g i a) = _`. Rewrite using `[map_mul, hπa ((1 : E) ⊗ₜ[F] _), halg]`. Use `show u i * ((N : ℕ) : w.adicCompletion F)⁻¹ * ρ (((N : E) • ((B : Matrix (Fin k) (Fin k) E) *ᵥ Pi.single i 1)) a) = _`. Rewrite using `[Pi.smul_apply, smul_eq_mul, hB, map_mul, map_natCast]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[← hπa, Finset.sum_apply, map_sum, ht]`. Simplify using `only [hterm]`. Simplify using `[Matrix.mulVec, dotProduct]`.
-/
theorem fr_lat_of {k : ℕ} (w : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] w.adicCompletion F ≃+* w.adicCompletion F × w.adicCompletion F)
    (halg : ∀ a : w.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = (a, a))
    (Λ : Submodule (𝓞 E) (Fin k → E)) (B : GL (Fin k) E)
    (h1 : ∀ x ∈ Λ, ∀ a, (((B⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ x) a ∈ (algebraMap (𝓞 E) E).range)
    (N : ℕ) (hN : (N : 𝓞 F) ∉ w.asIdeal)
    (h2 : ∀ i, (N : E) • ((B : Matrix (Fin k) (Fin k) E) *ᵥ Pi.single i 1) ∈ Λ)
    (t : Fin k → w.adicCompletion F) :
    (∃ x ∈ Formalism.L2.Herm.locL w Λ, ∀ a, (φ (x a)).1 = t a) ↔
      ∀ a, (((bc (((RingHom.fst _ _).comp φ.toRingHom).comp (inclE (F := F) (w.adicCompletion F))) B)⁻¹ :
        GL (Fin k) (w.adicCompletion F)) : Matrix (Fin k) (Fin k) (w.adicCompletion F)).mulVec t a ∈
          w.adicCompletionIntegers F := by
  set π : E ⊗[F] w.adicCompletion F →+* w.adicCompletion F := (RingHom.fst _ _).comp φ.toRingHom with hπ
  set ρ : E →+* w.adicCompletion F := π.comp (inclE (F := F) (w.adicCompletion F)) with hρ
  have hπa : ∀ s, π s = (φ s).1 := fun _ => rfl
  have hinv : (((bc ρ B)⁻¹ : GL (Fin k) (w.adicCompletion F)) : Matrix (Fin k) (Fin k) (w.adicCompletion F)) =
      ((B⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E).map ρ := by
    rw [← map_inv]; rfl
  have hval : ((bc ρ B : GL (Fin k) (w.adicCompletion F)) : Matrix (Fin k) (Fin k) (w.adicCompletion F)) =
      (B : Matrix (Fin k) (Fin k) E).map ρ := rfl
  constructor
  · rintro ⟨x, hx, hxt⟩
    have ht : t = fun a => π (x a) := funext fun a => (hxt a).symm
    rw [ht]
    clear ht hxt
    unfold Formalism.L2.Herm.locL latS at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      intro a
      have e1 : ((((B⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E).map ρ) *ᵥ
          (fun b => π (inclE (F := F) (w.adicCompletion F) (l b)))) a =
          ρ ((((B⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ l) a) :=
        (RingHom.map_mulVec ρ _ l a).symm
      rw [hinv, e1]
      obtain ⟨y, hy⟩ := h1 l hl a
      rw [← hy]
      exact hom_int w ρ y
    | zero =>
      intro a
      have : (fun b => π ((0 : Fin k → E ⊗[F] w.adicCompletion F) b)) = 0 := by
        funext b; simp
      rw [this, mulVec_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      intro a
      have : (fun b => π ((x + y) b)) = (fun b => π (x b)) + fun b => π (y b) := by
        funext b; simp
      rw [this, mulVec_add]
      exact add_mem (hx a) (hy a)
    | smul s x _ hx =>
      intro a
      have : (fun b => π ((s • x) b)) = π (s : E ⊗[F] w.adicCompletion F) • fun b => π (x b) := by
        funext b
        show π ((s : E ⊗[F] w.adicCompletion F) * x b) = π (s : E ⊗[F] w.adicCompletion F) * π (x b)
        rw [map_mul]
      rw [this, mulVec_smul]
      exact mul_mem (fst_int w φ halg _ s.2) (hx a)
  · intro hu
    set u : Fin k → w.adicCompletion F :=
      (((bc ρ B)⁻¹ : GL (Fin k) (w.adicCompletion F)) : Matrix (Fin k) (Fin k) (w.adicCompletion F)) *ᵥ t with hudef
    have ht : t = (B : Matrix (Fin k) (Fin k) E).map ρ *ᵥ u := by
      rw [← hval, hudef, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    have hNv : Valued.v ((N : ℕ) : w.adicCompletion F) = 1 := by
      have := Formalism.MainNotions.Gaps.LG.sc_val_one w (N : 𝓞 F) hN
      simpa using this
    have hN0 : ((N : ℕ) : w.adicCompletion F) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hNv
      exact zero_ne_one hNv
    have hNi : ((N : ℕ) : w.adicCompletion F)⁻¹ ∈ w.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hNv, inv_one]
    let s : Fin k → intV E w := fun i =>
      ⟨(1 : E) ⊗ₜ[F] (u i * ((N : ℕ) : w.adicCompletion F)⁻¹),
        Formalism.MainNotions.Gaps.LG.sc_right_mem w _ (mul_mem (hu i) hNi)⟩
    let g : Fin k → Fin k → E ⊗[F] w.adicCompletion F := fun i a =>
      inclE (F := F) (w.adicCompletion F) (((N : E) • ((B : Matrix (Fin k) (Fin k) E) *ᵥ Pi.single i 1)) a)
    refine ⟨∑ i, s i • g i, ?_, fun a => ?_⟩
    · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h2 i, rfl⟩)
    · have hB : ∀ i, ((B : Matrix (Fin k) (Fin k) E) *ᵥ Pi.single i 1) a = (B : Matrix (Fin k) (Fin k) E) a i := by
        intro i
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      have hterm : ∀ i, π ((s i • g i) a) = ρ ((B : Matrix (Fin k) (Fin k) E) a i) * u i := by
        intro i
        show π (((1 : E) ⊗ₜ[F] (u i * ((N : ℕ) : w.adicCompletion F)⁻¹)) * g i a) = _
        rw [map_mul, hπa ((1 : E) ⊗ₜ[F] _), halg]
        show u i * ((N : ℕ) : w.adicCompletion F)⁻¹ *
          ρ (((N : E) • ((B : Matrix (Fin k) (Fin k) E) *ᵥ Pi.single i 1)) a) = _
        rw [Pi.smul_apply, smul_eq_mul, hB, map_mul, map_natCast]
        field_simp
      rw [← hπa, Finset.sum_apply, map_sum, ht]
      simp only [hterm]
      simp [Matrix.mulVec, dotProduct]

/- English proof (translation)
Use `fr_lat_of w φ halg _ 1 (fun x hx a => ?_) T hT (fun i => ?_) t` and prove the remaining obligations. Rewrite using `[inv_one, Units.val_one, one_mulVec]`. Take `⟨y, hy⟩` from `Formalism.MainNotions.Gaps.LG.iw_Lb_le_std k pz hx a (Set.mem_univ a)`. Conclude with `⟨y, hy⟩`. Rewrite using `[Units.val_one, one_mulVec]`.

Establish `h1 : (T : E) • (Pi.single i 1 : Fin k → E) = (if i.1 = 0 then pzc else (T : 𝓞 E)) • Formalism.MainNotions.Gaps.LG.lbVec k pz i`. Use function extensionality and compare the values at `j`. Unfold `Formalism.MainNotions.Gaps.LG.lbVec`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality.

Simplify using `only [Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, mul_one]`. Use `split_ifs`. Rewrite using `[← hpz, mul_comm]`. Both sides reduce to the same expression. Simplify using the standard rewrite rules.

Simplify using `only [Pi.smul_apply, Pi.single_eq_of_ne hj, smul_zero]`. Rewrite using `[h1]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem fr_lat_LbOf {k : ℕ} (w : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] w.adicCompletion F ≃+* w.adicCompletion F × w.adicCompletion F)
    (halg : ∀ a : w.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = (a, a))
    (pz pzc : 𝓞 E) (T : ℕ) (hpz : (pz : E) * (pzc : E) = (T : E)) (hT : (T : 𝓞 F) ∉ w.asIdeal)
    (t : Fin k → w.adicCompletion F) :
    (∃ x ∈ Formalism.L2.Herm.locL w (Formalism.MainNotions.Gaps.LG.LbOf k pz), ∀ a, (φ (x a)).1 = t a) ↔
      ∀ a, (((bc (((RingHom.fst _ _).comp φ.toRingHom).comp (inclE (F := F) (w.adicCompletion F)))
        (1 : GL (Fin k) E))⁻¹ :
        GL (Fin k) (w.adicCompletion F)) : Matrix (Fin k) (Fin k) (w.adicCompletion F)).mulVec t a ∈
          w.adicCompletionIntegers F := by
  refine fr_lat_of w φ halg _ 1 (fun x hx a => ?_) T hT (fun i => ?_) t
  · rw [inv_one, Units.val_one, one_mulVec]
    obtain ⟨y, hy⟩ := Formalism.MainNotions.Gaps.LG.iw_Lb_le_std k pz hx a (Set.mem_univ a)
    exact ⟨y, hy⟩
  · rw [Units.val_one, one_mulVec]
    have h1 : (T : E) • (Pi.single i 1 : Fin k → E) =
        (if i.1 = 0 then pzc else (T : 𝓞 E)) • Formalism.MainNotions.Gaps.LG.lbVec k pz i := by
      funext j
      unfold Formalism.MainNotions.Gaps.LG.lbVec
      by_cases hj : j = i
      · subst hj
        simp only [Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, mul_one]
        split_ifs
        · rw [← hpz, mul_comm]; rfl
        · simp
      · simp only [Pi.smul_apply, Pi.single_eq_of_ne hj, smul_zero]
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Formalism.MainNotions.Gaps.Loc

end
