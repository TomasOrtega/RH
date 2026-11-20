import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OverLatticeIffSelfDualOverBase
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.RootSplitting

section General

variable {F E K : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K]

/- English proof (translation)
The claim follows from `Algebra.TensorProduct.includeRight_injective (R := F) (A := E) (B := K) (algebraMap F E).injective h`.
-/
theorem one_tmul_injective {a b : K} (h : (1 : E) ⊗ₜ[F] a = (1 : E) ⊗ₜ[F] b) : a = b :=
  Algebra.TensorProduct.includeRight_injective (R := F) (A := E) (B := K)
    (algebraMap F E).injective h

/- English proof (translation)
Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`.
-/
theorem algebraMap_tmul (t : F) :
    (algebraMap F E t) ⊗ₜ[F] (1 : K) = (1 : E) ⊗ₜ[F] (algebraMap F K t) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

/- English proof (translation)
Establish `hli : LinearIndependent F ![(1 : E), θ]`. Rewrite using `[LinearIndependent.pair_iff' one_ne_zero]`. Introduce `a ha`. Conclude with `hθ ⟨a, by rw [← ha, Algebra.algebraMap_eq_smul_one]⟩`. Apply the tactic sequence `refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdeg]), ?_, ?_⟩ <;> simp`.
-/
theorem exists_basis (hdeg : Module.finrank F E = 2) (θ : E) (hθ : θ ∉ (algebraMap F E).range) :
    ∃ b : Module.Basis (Fin 2) F E, b 0 = 1 ∧ b 1 = θ := by
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro a ha
    exact hθ ⟨a, by rw [← ha, Algebra.algebraMap_eq_smul_one]⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdeg]), ?_, ?_⟩ <;> simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨b.repr x 0, b.repr x 1, by have := b.sum_repr x rw [Fin.sum_univ_two, h0, h1] at this exact this.symm⟩`.
-/
theorem exists_coord (b : Module.Basis (Fin 2) F E) {θ : E} (h0 : b 0 = 1) (h1 : b 1 = θ) (x : E) :
    ∃ p q : F, x = p • (1 : E) + q • θ :=
  ⟨b.repr x 0, b.repr x 1, by
    have := b.sum_repr x
    rw [Fin.sum_univ_two, h0, h1] at this
    exact this.symm⟩

/- English proof (translation)
Set `f : E →ₗ[F] K` to `b.constr F ![1, r]`. Establish `f0 : f 1 = 1` using `by rw [← h0]; simp [f]`. Establish `f1 : f θ = r` using `by rw [← h1]; simp [f]`. Use `⟨AlgHom.ofLinearMap f f0 fun x y => ?_, f1⟩` and prove the remaining obligations. Take `⟨p, q, rfl⟩` from `exists_coord b h0 h1 x`.

Take `⟨p', q', rfl⟩` from `exists_coord b h0 h1 y`. Simplify using `only [mul_add, add_mul, smul_mul_smul_comm, one_mul, mul_one, hθ, hr, map_add, map_smul, f0, f1]`.
-/
theorem exists_algHom (b : Module.Basis (Fin 2) F E) {θ : E} (h0 : b 0 = 1) (h1 : b 1 = θ)
    (t n : F) (hθ : θ * θ = (-n) • (1 : E) + t • θ) (r : K) (hr : r * r = (-n) • (1 : K) + t • r) :
    ∃ φ : E →ₐ[F] K, φ θ = r := by
  let f : E →ₗ[F] K := b.constr F ![1, r]
  have f0 : f 1 = 1 := by rw [← h0]; simp [f]
  have f1 : f θ = r := by rw [← h1]; simp [f]
  refine ⟨AlgHom.ofLinearMap f f0 fun x y => ?_, f1⟩
  obtain ⟨p, q, rfl⟩ := exists_coord b h0 h1 x
  obtain ⟨p', q', rfl⟩ := exists_coord b h0 h1 y
  simp only [mul_add, add_mul, smul_mul_smul_comm, one_mul, mul_one, hθ, hr, map_add, map_smul,
    f0, f1]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, 0, by simp⟩`. Consider the case `tmul e k`. Take `⟨p, q, rfl⟩` from `exists_coord b h0 h1 e`. Conclude with `⟨p • k, q • k, by rw [TensorProduct.add_tmul, TensorProduct.smul_tmul, TensorProduct.smul_tmul]⟩`.

Consider the case `add x y hx hy`. Take `⟨a, c, rfl⟩` from `hx`. Take `⟨a', c', rfl⟩` from `hy`. Conclude with `⟨a + a', c + c', by rw [TensorProduct.tmul_add, TensorProduct.tmul_add]; abel⟩`.
-/
theorem exists_tensor_coord (b : Module.Basis (Fin 2) F E) {θ : E} (h0 : b 0 = 1) (h1 : b 1 = θ)
    (x : E ⊗[F] K) : ∃ a c : K, x = (1 : E) ⊗ₜ[F] a + θ ⊗ₜ[F] c := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul e k =>
    obtain ⟨p, q, rfl⟩ := exists_coord b h0 h1 e
    exact ⟨p • k, q • k, by rw [TensorProduct.add_tmul, TensorProduct.smul_tmul,
      TensorProduct.smul_tmul]⟩
  | add x y hx hy =>
    obtain ⟨a, c, rfl⟩ := hx
    obtain ⟨a', c', rfl⟩ := hy
    exact ⟨a + a', c + c', by rw [TensorProduct.tmul_add, TensorProduct.tmul_add]; abel⟩

/- English proof (translation)
Take `⟨t, ht'⟩` from `hfix (θ + σ θ) (by rw [map_add, hσ, add_comm])`. Take `⟨n, hn'⟩` from `hfix (θ * σ θ) (by rw [map_mul, hσ, mul_comm])`. Establish `htK : algebraMap F K t = r + r'`. Rewrite `ht` using `[← ht', algebraMap_tmul]`. Conclude with `one_tmul_injective ht`.

Establish `hnK : algebraMap F K n = r * r'`. Rewrite `hn` using `[← hn', algebraMap_tmul]`. Conclude with `one_tmul_injective hn`. Establish `hθ : θ ∉ (algebraMap F E).range`. Introduce and unpack `⟨a, rfl⟩`.

Rewrite `ht'` using `[AlgHom.commutes, ← map_add]`. Rewrite `hn'` using `[AlgHom.commutes, ← map_mul]`. Take `rfl` from `(algebraMap F E).injective ht'`. Take `rfl` from `(algebraMap F E).injective hn'`. Rewrite `htK` using `[map_add]`.

Rewrite `hnK` using `[map_mul]`. Apply `hne` to reduce the goal to its premises. Establish `: (r - r') ^ 2 = 0`. Take the linear combination `(-(r + r' + 2 * algebraMap F K a)) * htK + 4 * hnK`. Conclude with `pow_eq_zero_iff two_ne_zero |>.1 this`.

Take `⟨b, h0, h1⟩` from `exists_basis hdeg θ hθ`. Take `⟨φ, hφ⟩` from `exists_algHom b h0 h1 t n (by simp only [Algebra.smul_def, map_neg, ht', hn']; ring) r (by simp only [Algebra.smul_def, map_neg, htK, hnK]; ring)`. Establish `hφ' : φ (σ θ) = r'`. Use `congrArg φ ht'` as an intermediate fact. Rewrite `this` using `[AlgHom.commutes, map_add, hφ, htK]`.

Conclude with `(add_left_cancel this).symm`. Set `g : E ⊗[F] K →ₐ[F] K × K` to `(Algebra.TensorProduct.lift φ (AlgHom.id F K) fun _ _ => Commute.all _ _).prod (Algebra.TensorProduct.lift (φ.comp σ) (AlgHom.id F K) fun _ _ => Commute.all _ _)`. Establish `hg : ∀ (e : E) (k : K), g (e ⊗ₜ[F] k) = (φ e * k, φ (σ e) * k)` using `fun e k => rfl`. Establish `hg2 : ∀ a c : K, g ((1 : E) ⊗ₜ[F] a + θ ⊗ₜ[F] c) = (a + r * c, a + r' * c)`. Introduce `a c`.

Rewrite using `[map_add, hg, hg, hφ, hφ']`. Simplify using the standard rewrite rules. Use `⟨RingEquiv.ofBijective g ⟨?_, ?_⟩, φ, hφ, hφ', hg⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`.

Take `⟨a, c, rfl⟩` from `exists_tensor_coord b h0 h1 x`. Rewrite `hx` using `[hg2, Prod.mk_eq_zero]`. Establish `hc : c = 0`. Establish `: (r - r') * c = 0` using `by linear_combination hx.1 - hx.2`. Conclude with `(mul_eq_zero.1 this).resolve_left hne`.

Establish `ha : a = 0` using `by simpa [hc] using hx.1`. Simplify using `[ha, hc]`. Introduce and unpack `⟨a, c⟩`. Use `⟨(1 : E) ⊗ₜ[F] (c - r' * ((a - c) / (r - r'))) + θ ⊗ₜ[F] ((a - c) / (r - r')), ?_⟩` and prove the remaining obligations. Rewrite using `[hg2]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_ringEquiv (σ : E →ₐ[F] E) (hdeg : Module.finrank F E = 2) (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x, σ x = x → x ∈ (algebraMap F E).range) (θ : E) (r r' : K) (hne : r - r' ≠ 0)
    (ht : (θ + σ θ) ⊗ₜ[F] (1 : K) = (1 : E) ⊗ₜ[F] (r + r'))
    (hn : (θ * σ θ) ⊗ₜ[F] (1 : K) = (1 : E) ⊗ₜ[F] (r * r')) :
    ∃ (s : E ⊗[F] K ≃+* K × K) (φ : E →ₐ[F] K), φ θ = r ∧ φ (σ θ) = r' ∧
      ∀ (e : E) (k : K), s (e ⊗ₜ[F] k) = (φ e * k, φ (σ e) * k) := by
  obtain ⟨t, ht'⟩ := hfix (θ + σ θ) (by rw [map_add, hσ, add_comm])
  obtain ⟨n, hn'⟩ := hfix (θ * σ θ) (by rw [map_mul, hσ, mul_comm])
  have htK : algebraMap F K t = r + r' := by
    rw [← ht', algebraMap_tmul] at ht; exact one_tmul_injective ht
  have hnK : algebraMap F K n = r * r' := by
    rw [← hn', algebraMap_tmul] at hn; exact one_tmul_injective hn
  have hθ : θ ∉ (algebraMap F E).range := by
    rintro ⟨a, rfl⟩
    rw [AlgHom.commutes, ← map_add] at ht'
    rw [AlgHom.commutes, ← map_mul] at hn'
    obtain rfl := (algebraMap F E).injective ht'
    obtain rfl := (algebraMap F E).injective hn'
    rw [map_add] at htK
    rw [map_mul] at hnK
    apply hne
    have : (r - r') ^ 2 = 0 := by
      linear_combination (-(r + r' + 2 * algebraMap F K a)) * htK + 4 * hnK
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  obtain ⟨b, h0, h1⟩ := exists_basis hdeg θ hθ
  obtain ⟨φ, hφ⟩ := exists_algHom b h0 h1 t n
    (by simp only [Algebra.smul_def, map_neg, ht', hn']; ring) r
    (by simp only [Algebra.smul_def, map_neg, htK, hnK]; ring)
  have hφ' : φ (σ θ) = r' := by
    have := congrArg φ ht'
    rw [AlgHom.commutes, map_add, hφ, htK] at this
    exact (add_left_cancel this).symm
  let g : E ⊗[F] K →ₐ[F] K × K :=
    (Algebra.TensorProduct.lift φ (AlgHom.id F K) fun _ _ => Commute.all _ _).prod
      (Algebra.TensorProduct.lift (φ.comp σ) (AlgHom.id F K) fun _ _ => Commute.all _ _)
  have hg : ∀ (e : E) (k : K), g (e ⊗ₜ[F] k) = (φ e * k, φ (σ e) * k) := fun e k => rfl
  have hg2 : ∀ a c : K, g ((1 : E) ⊗ₜ[F] a + θ ⊗ₜ[F] c) = (a + r * c, a + r' * c) := by
    intro a c
    rw [map_add, hg, hg, hφ, hφ']; simp
  refine ⟨RingEquiv.ofBijective g ⟨?_, ?_⟩, φ, hφ, hφ', hg⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, c, rfl⟩ := exists_tensor_coord b h0 h1 x
    rw [hg2, Prod.mk_eq_zero] at hx
    have hc : c = 0 := by
      have : (r - r') * c = 0 := by linear_combination hx.1 - hx.2
      exact (mul_eq_zero.1 this).resolve_left hne
    have ha : a = 0 := by simpa [hc] using hx.1
    simp [ha, hc]
  · rintro ⟨a, c⟩
    refine ⟨(1 : E) ⊗ₜ[F] (c - r' * ((a - c) / (r - r'))) + θ ⊗ₜ[F] ((a - c) / (r - r')), ?_⟩
    rw [hg2]
    congr 1
    · field_simp; ring
    · ring

end General

/- English proof (translation)
Take `⟨u, hu'⟩` from `hu.exists_right_inv`. Establish `huK : ((r : v.adicCompletion F) - r') * u = 1` using `by exact_mod_cast congrArg Subtype.val hu'`. Establish `hne : (r : v.adicCompletion F) - r' ≠ 0` using `left_ne_zero_of_mul_eq_one huK`. Take `⟨s, φ, h1, h2, hs⟩` from `exists_ringEquiv σ hdeg hσ hfix θ _ _ hne ht hn`. Establish `hint : ∀ x : E, IsIntegral ℤ x → φ x ∈ v.adicCompletionIntegers F`.

Introduce `x hx`. Take `⟨p, hp, hp0⟩` from `map_isIntegral_int φ hx`. Establish `h4 : IsIntegral (v.adicCompletionIntegers F) (φ x)` using `⟨p.map (Int.castRingHom _), hp.map _, by`. Rewrite using `[Polynomial.eval₂_map]`. Conclude with `(congrArg (fun f => Polynomial.eval₂ f (φ x) p) (RingHom.ext_int _ _)).trans hp0⟩`.

Take `⟨y, hy⟩` from `IsIntegrallyClosed.algebraMap_eq_of_integral h4`. Conclude with `hy ▸ y.2`. Establish `hone : ∀ a : v.adicCompletion F, s ((1 : E) ⊗ₜ[F] a) = (a, a)`. Introduce `a`. Rewrite using `[hs]`.

Simplify using the standard rewrite rules. Use `⟨s, ⟨hone, fun x => ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩, by rw [hs, h1, h2]; simp⟩` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul e k`.

Establish `: sigR σ (v.adicCompletion F) (e ⊗ₜ[F] k) = σ e ⊗ₜ[F] k` using `rfl`. Rewrite using `[this, hs, hs, hσ]`. Both sides reduce to the same expression. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Proceed by induction on `hx using Subring.closure_induction with`.

Consider the case `mem x hx`. Break down `hx with ⟨⟨_, a, rfl⟩, rfl⟩ | ⟨a, rfl⟩` into its components or cases. Simplify using `only [hs, mul_one]`. Conclude with `⟨hint _ a.2, hint _ (IsIntegral.map (σ : E →+* E).toIntAlgHom a.2)⟩`. Simplify using `only [hone]`.

Conclude with `⟨a.2, a.2⟩`. Consider the case `zero => simp`. Consider the case `one => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩`.

Consider the case `neg x _ hx => rw [map_neg]`. Conclude with `⟨neg_mem hx.1, neg_mem hx.2⟩`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`. Conclude with `⟨mul_mem hx.1 hy.1, mul_mem hx.2 hy.2⟩`. Establish `hm : ∀ a ∈ v.adicCompletionIntegers F, (1 : E) ⊗ₜ[F] a ∈ intV E v` using `fun a ha => Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)`.

Establish `hθm : θ ⊗ₜ[F] (1 : v.adicCompletion F) ∈ intV E v` using `GlobalTheory.OverCompare.tmul_mem_intV (⟨θ, hθ⟩ : 𝓞 E)`. Establish `hc : ((s x).1 - (s x).2) * u ∈ v.adicCompletionIntegers F` using `mul_mem (sub_mem hx.1 hx.2) u.2`. Establish `: x = (1 : E) ⊗ₜ[F] ((s x).2 - r' * (((s x).1 - (s x).2) * u)) + θ ⊗ₜ[F] (1 : v.adicCompletion F) * (1 : E) ⊗ₜ[F] (((s x).1 - (s x).2) * u)`. Apply `s.injective` to reduce the goal to its premises. Rewrite using `[map_add, map_mul, hone, hone, hs, h1, h2]`.

Apply `Prod.ext` to reduce the goal to its premises. Simplify using `only [Prod.fst_add, Prod.fst_mul]`. Take the linear combination `(-((s x).1 - (s x).2)) * huK`. Simplify using `only [Prod.snd_add, Prod.snd_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `add_mem (hm _ (sub_mem hx.2 (mul_mem r'.2 hc))) (mul_mem hθm (hm _ hc))`.
-/
theorem exists_isSplitting (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hdeg : Module.finrank F E = 2) (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x, σ x = x → x ∈ (algebraMap F E).range) (v : HeightOneSpectrum (𝓞 F)) (θ : E)
    (r r' : v.adicCompletionIntegers F) (hθ : IsIntegral ℤ θ) (hu : IsUnit (r - r'))
    (ht : (θ + σ θ) ⊗ₜ[F] (1 : v.adicCompletion F) =
      (1 : E) ⊗ₜ[F] ((r : v.adicCompletion F) + r'))
    (hn : (θ * σ θ) ⊗ₜ[F] (1 : v.adicCompletion F) =
      (1 : E) ⊗ₜ[F] ((r : v.adicCompletion F) * r')) :
    ∃ s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F,
      IsSplitting σ v s ∧
      s (θ ⊗ₜ[F] (1 : v.adicCompletion F)) =
        ((r : v.adicCompletion F), (r' : v.adicCompletion F)) := by
  obtain ⟨u, hu'⟩ := hu.exists_right_inv
  have huK : ((r : v.adicCompletion F) - r') * u = 1 := by exact_mod_cast congrArg Subtype.val hu'
  have hne : (r : v.adicCompletion F) - r' ≠ 0 := left_ne_zero_of_mul_eq_one huK
  obtain ⟨s, φ, h1, h2, hs⟩ := exists_ringEquiv σ hdeg hσ hfix θ _ _ hne ht hn
  have hint : ∀ x : E, IsIntegral ℤ x → φ x ∈ v.adicCompletionIntegers F := by
    intro x hx
    obtain ⟨p, hp, hp0⟩ := map_isIntegral_int φ hx
    have h4 : IsIntegral (v.adicCompletionIntegers F) (φ x) :=
      ⟨p.map (Int.castRingHom _), hp.map _, by
        rw [Polynomial.eval₂_map]
        exact (congrArg (fun f => Polynomial.eval₂ f (φ x) p) (RingHom.ext_int _ _)).trans hp0⟩
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h4
    exact hy ▸ y.2
  have hone : ∀ a : v.adicCompletion F, s ((1 : E) ⊗ₜ[F] a) = (a, a) := by
    intro a; rw [hs]; simp
  refine ⟨s, ⟨hone, fun x => ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩, by rw [hs, h1, h2]; simp⟩
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul e k =>
      have : sigR σ (v.adicCompletion F) (e ⊗ₜ[F] k) = σ e ⊗ₜ[F] k := rfl
      rw [this, hs, hs, hσ]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  · induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨⟨_, a, rfl⟩, rfl⟩ | ⟨a, rfl⟩
      · simp only [hs, mul_one]
        exact ⟨hint _ a.2, hint _ (IsIntegral.map (σ : E →+* E).toIntAlgHom a.2)⟩
      · simp only [hone]; exact ⟨a.2, a.2⟩
    | zero => simp
    | one => simp
    | add x y _ _ hx hy => rw [map_add]; exact ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
    | neg x _ hx => rw [map_neg]; exact ⟨neg_mem hx.1, neg_mem hx.2⟩
    | mul x y _ _ hx hy => rw [map_mul]; exact ⟨mul_mem hx.1 hy.1, mul_mem hx.2 hy.2⟩
  · have hm : ∀ a ∈ v.adicCompletionIntegers F, (1 : E) ⊗ₜ[F] a ∈ intV E v := fun a ha =>
      Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
    have hθm : θ ⊗ₜ[F] (1 : v.adicCompletion F) ∈ intV E v :=
      GlobalTheory.OverCompare.tmul_mem_intV (⟨θ, hθ⟩ : 𝓞 E)
    have hc : ((s x).1 - (s x).2) * u ∈ v.adicCompletionIntegers F :=
      mul_mem (sub_mem hx.1 hx.2) u.2
    have : x = (1 : E) ⊗ₜ[F] ((s x).2 - r' * (((s x).1 - (s x).2) * u)) +
        θ ⊗ₜ[F] (1 : v.adicCompletion F) * (1 : E) ⊗ₜ[F] (((s x).1 - (s x).2) * u) := by
      apply s.injective
      rw [map_add, map_mul, hone, hone, hs, h1, h2]
      apply Prod.ext
      · simp only [Prod.fst_add, Prod.fst_mul]
        linear_combination (-((s x).1 - (s x).2)) * huK
      · simp only [Prod.snd_add, Prod.snd_mul]; ring
    rw [this]
    exact add_mem (hm _ (sub_mem hx.2 (mul_mem r'.2 hc))) (mul_mem hθm (hm _ hc))

end GlobalTheory.RootSplitting
