import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceStableArchimedeanMaximalCompaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartInvariantSubmoduleDenseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartCompactStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactLeviLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairDescentCaseBStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBMatchedIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaLiftCompatible
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.BranchMapB

open GlobalTheory.TwPartStab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Use `⟨fun u hu => ?_, fun w => ?_⟩` and prove the remaining obligations. Establish `e : mat (k * k') - 1 = (mat k - 1) * mat k' + (mat k' - 1)`. Express the relevant statement in the definitionally equal form `mat k * mat k' - 1 = _`. Rewrite using `[Matrix.sub_mul, Matrix.one_mul]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e, smul_add, ← Matrix.smul_mul, hk.1 u hu, hk'.1 u hu, Matrix.zero_mul, add_zero]`. Express the relevant statement in the definitionally equal form `Commute ((mat k * mat k').map (piInf (τ w))) (X.θ w)`. Rewrite using `[Matrix.map_mul]`. Conclude with `(hk.2 w).mul_left (hk'.2 w)`.
-/
theorem kInf_mul {n : ℕ} {X : Spc F E n} {τ : ∀ w : InfinitePlace F, EmbOver E w} {k k' : UA σ X.J}
    (hk : k ∈ KInf σ X τ) (hk' : k' ∈ KInf σ X τ) : k * k' ∈ KInf σ X τ := by
  refine ⟨fun u hu => ?_, fun w => ?_⟩
  · have e : mat (k * k') - 1 = (mat k - 1) * mat k' + (mat k' - 1) := by
      change mat k * mat k' - 1 = _
      rw [Matrix.sub_mul, Matrix.one_mul]
      abel
    rw [e, smul_add, ← Matrix.smul_mul, hk.1 u hu, hk'.1 u hu, Matrix.zero_mul, add_zero]
  · change Commute ((mat k * mat k').map (piInf (τ w))) (X.θ w)
    rw [Matrix.map_mul]
    exact (hk.2 w).mul_left (hk'.2 w)

/- English proof (translation)
Use `⟨fun u _ => ?_, fun w => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `u • ((1 : Matrix (Fin n) (Fin n) (AE F E)) - 1) = 0`. Rewrite using `[sub_self, smul_zero]`. Express the relevant statement in the definitionally equal form `Commute ((1 : Matrix (Fin n) (Fin n) (AE F E)).map (piInf (τ w))) (X.θ w)`. Rewrite using `[Matrix.map_one _ (map_zero _) (map_one _)]`.

Conclude with `Commute.one_left _`.
-/
theorem kInf_one {n : ℕ} {X : Spc F E n} {τ : ∀ w : InfinitePlace F, EmbOver E w} : (1 : UA σ X.J) ∈ KInf σ X τ := by
  refine ⟨fun u _ => ?_, fun w => ?_⟩
  · change u • ((1 : Matrix (Fin n) (Fin n) (AE F E)) - 1) = 0
    rw [sub_self, smul_zero]
  · change Commute ((1 : Matrix (Fin n) (Fin n) (AE F E)).map (piInf (τ w))) (X.θ w)
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact Commute.one_left _

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ _ = _`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ _ = _`. Simplify using the standard rewrite rules.

Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin d) (Fin d) (AE F E)) * _ = _ * (1 : Matrix (Fin d₁) (Fin d₁) (AE F E))`. Simplify using the standard rewrite rules.
-/
theorem isLevi_one {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} (H' : Plane E d d₁) :
    IsLevi H' 1 (1 : UA σ W₁.J) (1 : UA σ W.J) := by
  refine ⟨?_, ?_, ?_⟩
  · change (1 : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ _ = _
    simp
  · change (1 : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ _ = _
    simp
  · change (1 : Matrix (Fin d) (Fin d) (AE F E)) * _ = _ * (1 : Matrix (Fin d₁) (Fin d₁) (AE F E))
    simp

/- English proof (translation)
Take `⟨hx, hy, hι⟩` from `h`. Take `⟨hx', hy', hι'⟩` from `h'`. Simplify using `only [Units.val_one, one_smul, inv_one, map_one] at hx hy hx' hy' ⊢`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(mat k * mat k') *ᵥ _ = _`.

Rewrite using `[← Matrix.mulVec_mulVec, hx', hx]`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `(mat k * mat k') *ᵥ _ = _`. Rewrite using `[← Matrix.mulVec_mulVec, hy', hy]`. Simplify using the standard rewrite rules.

Express the relevant statement in the definitionally equal form `mat k * mat k' * _ = _ * (mat k₁ * mat k₁')`. Rewrite using `[Matrix.mul_assoc, hι', ← Matrix.mul_assoc, hι, Matrix.mul_assoc]`.
-/
theorem isLevi_mul {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {k₁ k₁' : UA σ W₁.J}
    {k k' : UA σ W.J} (h : IsLevi H' 1 k₁ k) (h' : IsLevi H' 1 k₁' k') : IsLevi H' 1 (k₁ * k₁') (k * k') := by
  obtain ⟨hx, hy, hι⟩ := h
  obtain ⟨hx', hy', hι'⟩ := h'
  simp only [Units.val_one, one_smul, inv_one, map_one] at hx hy hx' hy' ⊢
  refine ⟨?_, ?_, ?_⟩
  · change (mat k * mat k') *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, hx', hx]; simp
  · change (mat k * mat k') *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, hy', hy]; simp
  · change mat k * mat k' * _ = _ * (mat k₁ * mat k₁')
    rw [Matrix.mul_assoc, hι', ← Matrix.mul_assoc, hι, Matrix.mul_assoc]

/- English proof (translation)
Introduce `r _`. Establish `e : ((1 : UA σ Y.J), (1 : UA σ W.J)) = 1` using `rfl`. Rewrite using `[e, map_one]`. Both sides reduce to the same expression.
-/
theorem acts_one {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (om : Rep σ Y W) (f : SInf F (Fin n × Fin d)) :
    Acts (evI F) (om (1, 1)) f f := by
  intro r _
  have e : ((1 : UA σ Y.J), (1 : UA σ W.J)) = 1 := rfl
  rw [e, map_one]
  rfl

end GlobalTheory.BranchMapB

namespace GlobalTheory.BranchMapB

open GlobalTheory.TwPartStab

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B a b G G₁ H H' hcfg X om om' R Rf om₁ om₁' R₁ Rf₁ hm hm₁`. Take `⟨g₀, hg₀, f₀, hf₀, hwT, hw0, hrel⟩` from `GlobalTheory.T.matched_pair_descent_case_b hKP F E σ B a b G G₁ H H' hcfg X om om' R Rf om₁ om₁' R₁ Rf₁ hm hm₁`. Establish `hB` using `hm.triple.base`. Establish `hM` using `hm.triple.geo.hM`. Establish `hw` using `hm.triple.weil`.

Establish `hM₁` using `hm₁.triple.geo.hM`. Establish `hw₁` using `hm₁.triple.weil`. Establish `hL` using `GlobalTheory.T.archActionReadings_compatible F (Fin a × Fin (a + (b + 2)))`. Establish `hL₁` using `GlobalTheory.T.archActionReadings_compatible F (Fin a × Fin (a + b))`. Establish `hop : ∀ k ∈ KInf σ G.W B.emb, ∃ A : SInf F (Fin a × Fin (a + (b + 2))) →ₗ[ℂ] SInf F (Fin a × Fin (a + (b + 2))), (∀ f : SInf F (Fin a × Fin (a + (b + 2))), Acts (evI F) (om (1, k)) f (A f)) ∧ ∃ T : R.Pi →ₗ[ℂ] R.Pi, ∀ g ∈ G.M.Pol B.ψ B.emb, R.p (A g) = T (R.p g)`.

Introduce `k hk`. Take `⟨A, hA⟩` from `GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B _ _ G.V G.W G.M om X.β (X.β / X.α) hB hM hw k hk`. Use `⟨A, hA, descent R.p hm.real.quot.onto A fun f hf hpf => ?_⟩` and prove the remaining obligations. Establish `h0` using `hm.real.cpt k hk f hf 0 (zero_mem _) (A f) 0 (hA f) (acts_zero _) (by rw [hpf, map_zero])`. Rewrite using `[h0, map_zero]`.

Establish `hop₁ : ∀ k ∈ KInf σ G₁.W B.emb, ∃ A : SInf F (Fin a × Fin (a + b)) →ₗ[ℂ] SInf F (Fin a × Fin (a + b)), (∀ f : SInf F (Fin a × Fin (a + b)), Acts (evI F) (om₁ (1, k)) f (A f)) ∧ ∃ T : R₁.Pi →ₗ[ℂ] R₁.Pi, ∀ g ∈ G₁.M.Pol B.ψ B.emb, R₁.p (A g) = T (R₁.p g)`. Introduce `k hk`. Take `⟨A, hA⟩` from `GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B _ _ G₁.V G₁.W G₁.M om₁ X.β (X.β / X.α) hB hM₁ hw₁ k hk`. Use `⟨A, hA, descent R₁.p hm₁.real.quot.onto A fun f hf hpf => ?_⟩` and prove the remaining obligations. Establish `h0` using `hm₁.real.cpt k hk f hf 0 (zero_mem _) (A f) 0 (hA f) (acts_zero _) (by rw [hpf, map_zero])`.

Rewrite using `[h0, map_zero]`. Use `choose A hA T hT using hop`. Use `choose A₁ hA₁ T₁ hT₁ using hop₁`. Establish `hpol : ∀ k (hk : k ∈ KInf σ G.W B.emb), ∀ g ∈ G.M.Pol B.ψ B.emb, A k hk g ∈ G.M.Pol B.ψ B.emb` using `fun k hk g hg => GlobalTheory.T.polynomialFockSpace_stable_archimedeanMaximalCompact F E σ B _ _ G.V G.W G.M om X.β (X.β / X.α) hB hM hw k hk g hg _ (hA k hk g)`. Establish `hpol₁ : ∀ k (hk : k ∈ KInf σ G₁.W B.emb), ∀ g ∈ G₁.M.Pol B.ψ B.emb, A₁ k hk g ∈ G₁.M.Pol B.ψ B.emb` using `fun k hk g hg => GlobalTheory.T.polynomialFockSpace_stable_archimedeanMaximalCompact F E σ B _ _ G₁.V G₁.W G₁.M om₁ X.β (X.β / X.α) hB hM₁ hw₁ k hk g hg _ (hA₁ k hk g)`.

Establish `hg₀P : g₀ ∈ G₁.M.Pol B.ψ B.emb` using `fockDeg_le_pol _ _ _ _ hg₀`. Establish `hlift` using `GlobalTheory.T.max_compact_levi_lift F E σ B a b G G₁ H H' hcfg hB hm.triple.geo hm₁.triple.geo`. Use `choose Lf hLfK hLfL using hlift`. Establish `hswap : ∀ (k k' : UA σ G.W.J) (k₁ k₁' : UA σ G₁.W.J) (g g' : SInf F (Fin a × Fin (a + b))) (f f' : SInf F (Fin a × Fin (a + (b + 2)))), (k ∈ KInf σ G.W B.emb ∧ k₁ ∈ KInf σ G₁.W B.emb ∧ IsLevi H' 1 k₁ k ∧ Acts (evI F) (om₁ (1, k₁)) g₀ g ∧ Acts (evI F) (om (1, k)) f₀ f) → (k' ∈ KIn …`. Introduce `k k' k₁ k₁' g g' f f' h h' he`.

Use `hrel Bool Finset.univ (fun i => cond i 1 (-1)) (fun i => cond i k k') (fun i => cond i k₁ k₁') (fun i => cond i g g') (fun i => cond i f f') (fun i _ => by cases i; exacts [h', h]) (by simp [Fintype.sum_bool, he])` as an intermediate fact. Simplify `this` using `[Fintype.sum_bool, ← sub_eq_add_neg, sub_eq_zero]`. Establish `h1₁ : (1 : UA σ G₁.W.J) ∈ KInf σ G₁.W B.emb` using `kInf_one`. Establish `h1 : (1 : UA σ G.W.J) ∈ KInf σ G.W B.emb` using `kInf_one`. Establish `hv0 : R₁.p g₀ ≠ 0`.

Introduce `h0`. Apply `hw0` to reduce the goal to its premises. Use `hrel Unit Finset.univ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => g₀) (fun _ => f₀) (fun _ _ => ⟨h1, h1₁, isLevi_one H', acts_one om₁ g₀, acts_one om f₀⟩) (by simp [h0])` as an intermediate fact. Simplify using `using this`. Set `v : {k : UA σ G₁.W.J // k ∈ KInf σ G₁.W B.emb} → R₁.Pi` to `fun k => R₁.p (A₁ k.1 k.2 g₀)`.

Set `u : {k : UA σ G₁.W.J // k ∈ KInf σ G₁.W B.emb} → R.Pi` to `fun k => R.p (A (Lf k.1 k.2) (hLfK k.1 k.2) f₀)`. Set `ιv` to `Finsupp.linearCombination ℂ v`. Set `κv` to `Finsupp.linearCombination ℂ u`. Establish `hker : LinearMap.ker ιv ≤ LinearMap.ker κv`. Introduce `c hc`.

Rewrite `hc`, the goal using `[LinearMap.mem_ker]`. Simplify using `only [ιv, κv, Finsupp.linearCombination_apply, Finsupp.sum] at hc ⊢`. Conclude with `hrel _ c.support c (fun k => Lf k.1 k.2) (fun k => k.1) (fun k => A₁ k.1 k.2 g₀) (fun k => A (Lf k.1 k.2) (hLfK k.1 k.2) f₀) (fun k _ => ⟨hLfK k.1 k.2, k.2, hLfL k.1 k.2, hA₁ k.1 k.2 g₀, hA _ _ f₀⟩) hc`. Set `ψ₀ : LinearMap.range ιv →ₗ[ℂ] R.Pi` to `(LinearMap.ker ιv).liftQ κv hker ∘ₗ ιv.quotKerEquivRange.symm.toLinearMap`. Establish `hψ₀ : ∀ c, ψ₀ ⟨ιv c, LinearMap.mem_range_self ιv c⟩ = κv c`.

Introduce `c`. Express the relevant statement in the definitionally equal form `(LinearMap.ker ιv).liftQ κv hker (ιv.quotKerEquivRange.symm ⟨ιv c, LinearMap.mem_range_self ιv c⟩) = κv c`. Rewrite using `[LinearMap.quotKerEquivRange_symm_apply_image]`. Both sides reduce to the same expression. Take `⟨ψ, hψ⟩` from `LinearMap.exists_extend ψ₀`.

Establish `hψι : ∀ c, ψ (ιv c) = κv c` using `fun c => by`. Use `LinearMap.congr_fun hψ ⟨ιv c, LinearMap.mem_range_self ιv c⟩` as an intermediate fact. Rewrite `this` using `[LinearMap.comp_apply, hψ₀]`. Conclude with `this`. Establish `hψv : ∀ i, ψ (v i) = u i` using `fun i => by`.

Use `hψι (Finsupp.single i 1)` as an intermediate fact. Simplify `this` using `only [ιv, κv, Finsupp.linearCombination_single, one_smul]`. Establish `hTv : ∀ k₁ (hk₁ : k₁ ∈ KInf σ G₁.W B.emb) (i : {k : UA σ G₁.W.J // k ∈ KInf σ G₁.W B.emb}), T₁ k₁ hk₁ (v i) = v ⟨k₁ * i.1, kInf_mul hk₁ i.2⟩`. Introduce `k₁ hk₁ i`. Establish `c1` using `acts_mul hw₁ i.1 k₁ (hA₁ i.1 i.2 g₀) (hA₁ k₁ hk₁ (A₁ i.1 i.2 g₀))`.

Establish `e` using `(hL₁ _ _ _).2.2.2.1 _ c1 (hA₁ (k₁ * i.1) (kInf_mul hk₁ i.2) g₀)`. Express the relevant statement in the definitionally equal form `T₁ k₁ hk₁ (R₁.p (A₁ i.1 i.2 g₀)) = R₁.p (A₁ (k₁ * i.1) (kInf_mul hk₁ i.2) g₀)`. Rewrite using `[← hT₁ k₁ hk₁ _ (hpol₁ _ _ _ hg₀P), e]`. Establish `hv1 : v ⟨1, h1₁⟩ = R₁.p g₀`. Establish `e` using `(hL₁ _ _ _).2.2.2.1 _ (hA₁ 1 h1₁ g₀) (acts_one om₁ g₀)`.

Express the relevant statement in the definitionally equal form `R₁.p (A₁ 1 h1₁ g₀) = _`. Rewrite using `[e]`. Establish `hg₀V : R₁.p g₀ ∈ lowPartInf B G₁.M R₁.p` using `⟨g₀, hg₀, rfl⟩`. Establish `hspan : Submodule.span ℂ (Set.range v) = lowPartInf B G₁.M R₁.p`. Establish `hle : Submodule.span ℂ (Set.range v) ≤ lowPartInf B G₁.M R₁.p`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `(GlobalTheory.T.low_part_compact_stable hKP F E σ B a b G₁ X om₁ om₁' R₁ Rf₁ hm₁).1 i.1 i.2 g₀ hg₀P _ (hA₁ i.1 i.2 g₀) hg₀V`. Use `(GlobalTheory.T.lowPart_invariant_submodule_dense hKP F E σ B a b G₁ X om₁ om₁' R₁ Rf₁ hm₁ _ hle ?_).resolve_left ?_` and prove the remaining obligations. Introduce `k₁ hk₁ g hg g₁ hact hmem`.

Establish `e : g₁ = A₁ k₁ hk₁ g` using `(hL₁ _ _ _).2.2.2.1 _ hact (hA₁ k₁ hk₁ g)`. Rewrite using `[e, hT₁ k₁ hk₁ g hg]`. Establish `hst : Submodule.span ℂ (Set.range v) ≤ (Submodule.span ℂ (Set.range v)).comap (T₁ k₁ hk₁)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`.

Express the relevant statement in the definitionally equal form `T₁ k₁ hk₁ (v i) ∈ Submodule.span ℂ (Set.range v)`. Rewrite using `[hTv]`. Conclude with `Submodule.subset_span ⟨_, rfl⟩`. Conclude with `hst hmem`. Introduce `hbot`.

Apply `hv0` to reduce the goal to its premises. Rewrite using `[← hv1]`. Conclude with `(Submodule.eq_bot_iff _).1 hbot _ (Submodule.subset_span ⟨_, rfl⟩)`. Establish `hu1 : u ⟨1, h1₁⟩ = R.p f₀` using `hswap (Lf 1 h1₁) 1 1 1 g₀ g₀ _ f₀ ⟨hLfK 1 h1₁, h1₁, hLfL 1 h1₁, acts_one om₁ g₀, hA _ _ f₀⟩ ⟨h1, h1₁, isLevi_one H', acts_one om₁ g₀, acts_one om f₀⟩ rfl`. Use `⟨ψ, ⟨R₁.p g₀, hg₀V, by rw [← hv1, hψv, hu1]; exact hw0⟩, ?_, ?_⟩` and prove the remaining obligations.

Establish `hst` using `GlobalTheory.TwPartStabBeta.kStabL_twPart_beta hKP F E σ B a b G G₁ H H' hcfg X om om' R Rf om₁ om₁' R₁ Rf₁ hm hm₁`. Establish `hle : Submodule.span ℂ (Set.range v) ≤ (twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p)).comap ψ`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Express the relevant statement in the definitionally equal form `ψ (v i) ∈ twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p)`.

Rewrite using `[hψv]`. Conclude with `hst _ (hLfK i.1 i.2) i.1 i.2 (hLfL i.1 i.2) f₀ hf₀ _ (hA _ _ f₀) hwT`. Introduce `y hy`. Rewrite `hy` using `[← hspan]`. Conclude with `hle hy`.

Introduce `k hk k₁ hk₁ hL' g hg g₁ hact hgV f hf f₁ hactf hψg`. Establish `e₁ : g₁ = A₁ k₁ hk₁ g` using `(hL₁ _ _ _).2.2.2.1 _ hact (hA₁ k₁ hk₁ g)`. Establish `e : f₁ = A k hk f` using `(hL _ _ _).2.2.2.1 _ hactf (hA k hk f)`. Rewrite using `[e₁, e, hT₁ k₁ hk₁ g hg, hT k hk f hf, ← hψg]`. Rewrite `hgV` using `[← hspan]`.

Use `LinearMap.eqOn_span' (f := ψ ∘ₗ T₁ k₁ hk₁) (g := T k hk ∘ₗ ψ) ?_ hgV` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Express the relevant statement in the definitionally equal form `ψ (T₁ k₁ hk₁ (v i)) = T k hk (ψ (v i))`. Rewrite using `[hTv, hψv, hψv]`. Express the relevant statement in the definitionally equal form `R.p (A _ _ f₀) = T k hk (R.p (A _ _ f₀))`.

Rewrite using `[← hT k hk _ (hpol _ _ _ hf₀)]`. Conclude with `hswap (Lf (k₁ * i.1) (kInf_mul hk₁ i.2)) (k * Lf i.1 i.2) (k₁ * i.1) (k₁ * i.1) _ _ _ _ ⟨hLfK _ _, kInf_mul hk₁ i.2, hLfL _ _, hA₁ _ (kInf_mul hk₁ i.2) g₀, hA _ _ f₀⟩ ⟨kInf_mul hk (hLfK _ _), kInf_mul hk₁ i.2, isLevi_mul hL' (hLfL _ _), hA₁ _ (kInf_mul hk₁ i.2) g₀, acts_mul hw _ …`.
-/
theorem exists_map : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a (b + 2)) (Rf : FinMaps F a (b + 2))
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F a b) (Rf₁ : FinMaps F a b),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∃ ψ : R₁.Pi →ₗ[ℂ] R.Pi, (∃ y ∈ lowPartInf B G₁.M R₁.p, ψ y ≠ 0) ∧
        (∀ y ∈ lowPartInf B G₁.M R₁.p, ψ y ∈ (twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p))) ∧
        ∀ k ∈ KInf σ G.W B.emb, ∀ k₁ ∈ KInf σ G₁.W B.emb, IsLevi H' 1 k₁ k →
          ∀ g ∈ G₁.M.Pol B.ψ B.emb, ∀ g₁ : SInf F (Fin a × Fin (a + b)), Acts (evI F) (om₁ (1, k₁)) g g₁ →
          R₁.p g ∈ lowPartInf B G₁.M R₁.p → ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + (b + 2))),
          Acts (evI F) (om (1, k)) f f₁ → ψ (R₁.p g) = R.p f → ψ (R₁.p g₁) = R.p f₁ := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hcfg X om om' R Rf om₁ om₁' R₁ Rf₁ hm hm₁
  obtain ⟨g₀, hg₀, f₀, hf₀, hwT, hw0, hrel⟩ :=
    GlobalTheory.T.matched_pair_descent_case_b hKP F E σ B a b G G₁ H H' hcfg X om om' R Rf om₁ om₁' R₁ Rf₁ hm hm₁
  have hB := hm.triple.base
  have hM := hm.triple.geo.hM
  have hw := hm.triple.weil
  have hM₁ := hm₁.triple.geo.hM
  have hw₁ := hm₁.triple.weil
  have hL := GlobalTheory.T.archActionReadings_compatible F (Fin a × Fin (a + (b + 2)))
  have hL₁ := GlobalTheory.T.archActionReadings_compatible F (Fin a × Fin (a + b))
  have hop : ∀ k ∈ KInf σ G.W B.emb, ∃ A : SInf F (Fin a × Fin (a + (b + 2))) →ₗ[ℂ] SInf F (Fin a × Fin (a + (b + 2))),
      (∀ f : SInf F (Fin a × Fin (a + (b + 2))), Acts (evI F) (om (1, k)) f (A f)) ∧
      ∃ T : R.Pi →ₗ[ℂ] R.Pi, ∀ g ∈ G.M.Pol B.ψ B.emb, R.p (A g) = T (R.p g) := by
    intro k hk
    obtain ⟨A, hA⟩ := GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B _ _ G.V G.W G.M om X.β (X.β / X.α) hB hM hw k hk
    refine ⟨A, hA, descent R.p hm.real.quot.onto A fun f hf hpf => ?_⟩
    have h0 := hm.real.cpt k hk f hf 0 (zero_mem _) (A f) 0 (hA f) (acts_zero _) (by rw [hpf, map_zero])
    rw [h0, map_zero]
  have hop₁ : ∀ k ∈ KInf σ G₁.W B.emb, ∃ A : SInf F (Fin a × Fin (a + b)) →ₗ[ℂ] SInf F (Fin a × Fin (a + b)),
      (∀ f : SInf F (Fin a × Fin (a + b)), Acts (evI F) (om₁ (1, k)) f (A f)) ∧
      ∃ T : R₁.Pi →ₗ[ℂ] R₁.Pi, ∀ g ∈ G₁.M.Pol B.ψ B.emb, R₁.p (A g) = T (R₁.p g) := by
    intro k hk
    obtain ⟨A, hA⟩ := GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B _ _ G₁.V G₁.W G₁.M om₁ X.β (X.β / X.α) hB hM₁ hw₁ k hk
    refine ⟨A, hA, descent R₁.p hm₁.real.quot.onto A fun f hf hpf => ?_⟩
    have h0 := hm₁.real.cpt k hk f hf 0 (zero_mem _) (A f) 0 (hA f) (acts_zero _) (by rw [hpf, map_zero])
    rw [h0, map_zero]
  choose A hA T hT using hop
  choose A₁ hA₁ T₁ hT₁ using hop₁
  have hpol : ∀ k (hk : k ∈ KInf σ G.W B.emb), ∀ g ∈ G.M.Pol B.ψ B.emb, A k hk g ∈ G.M.Pol B.ψ B.emb := fun k hk g hg =>
    GlobalTheory.T.polynomialFockSpace_stable_archimedeanMaximalCompact F E σ B _ _ G.V G.W G.M om X.β (X.β / X.α) hB hM hw k hk g hg _ (hA k hk g)
  have hpol₁ : ∀ k (hk : k ∈ KInf σ G₁.W B.emb), ∀ g ∈ G₁.M.Pol B.ψ B.emb, A₁ k hk g ∈ G₁.M.Pol B.ψ B.emb :=
    fun k hk g hg => GlobalTheory.T.polynomialFockSpace_stable_archimedeanMaximalCompact F E σ B _ _ G₁.V G₁.W G₁.M om₁ X.β (X.β / X.α) hB hM₁ hw₁ k hk g hg _ (hA₁ k hk g)
  have hg₀P : g₀ ∈ G₁.M.Pol B.ψ B.emb := fockDeg_le_pol _ _ _ _ hg₀
  have hlift := GlobalTheory.T.max_compact_levi_lift F E σ B a b G G₁ H H' hcfg hB hm.triple.geo hm₁.triple.geo
  choose Lf hLfK hLfL using hlift

  have hswap : ∀ (k k' : UA σ G.W.J) (k₁ k₁' : UA σ G₁.W.J) (g g' : SInf F (Fin a × Fin (a + b)))
      (f f' : SInf F (Fin a × Fin (a + (b + 2)))),
      (k ∈ KInf σ G.W B.emb ∧ k₁ ∈ KInf σ G₁.W B.emb ∧ IsLevi H' 1 k₁ k ∧
        Acts (evI F) (om₁ (1, k₁)) g₀ g ∧ Acts (evI F) (om (1, k)) f₀ f) →
      (k' ∈ KInf σ G.W B.emb ∧ k₁' ∈ KInf σ G₁.W B.emb ∧ IsLevi H' 1 k₁' k' ∧
        Acts (evI F) (om₁ (1, k₁')) g₀ g' ∧ Acts (evI F) (om (1, k')) f₀ f') →
      R₁.p g = R₁.p g' → R.p f = R.p f' := by
    intro k k' k₁ k₁' g g' f f' h h' he
    have := hrel Bool Finset.univ (fun i => cond i 1 (-1)) (fun i => cond i k k') (fun i => cond i k₁ k₁')
      (fun i => cond i g g') (fun i => cond i f f') (fun i _ => by cases i; exacts [h', h]) (by simp [Fintype.sum_bool, he])
    simpa [Fintype.sum_bool, ← sub_eq_add_neg, sub_eq_zero] using this

  have h1₁ : (1 : UA σ G₁.W.J) ∈ KInf σ G₁.W B.emb := kInf_one
  have h1 : (1 : UA σ G.W.J) ∈ KInf σ G.W B.emb := kInf_one

  have hv0 : R₁.p g₀ ≠ 0 := by
    intro h0
    apply hw0
    have := hrel Unit Finset.univ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => g₀) (fun _ => f₀)
      (fun _ _ => ⟨h1, h1₁, isLevi_one H', acts_one om₁ g₀, acts_one om f₀⟩) (by simp [h0])
    simpa using this

  let v : {k : UA σ G₁.W.J // k ∈ KInf σ G₁.W B.emb} → R₁.Pi := fun k => R₁.p (A₁ k.1 k.2 g₀)
  let u : {k : UA σ G₁.W.J // k ∈ KInf σ G₁.W B.emb} → R.Pi := fun k => R.p (A (Lf k.1 k.2) (hLfK k.1 k.2) f₀)
  let ιv := Finsupp.linearCombination ℂ v
  let κv := Finsupp.linearCombination ℂ u
  have hker : LinearMap.ker ιv ≤ LinearMap.ker κv := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    simp only [ιv, κv, Finsupp.linearCombination_apply, Finsupp.sum] at hc ⊢
    exact hrel _ c.support c (fun k => Lf k.1 k.2) (fun k => k.1) (fun k => A₁ k.1 k.2 g₀)
      (fun k => A (Lf k.1 k.2) (hLfK k.1 k.2) f₀)
      (fun k _ => ⟨hLfK k.1 k.2, k.2, hLfL k.1 k.2, hA₁ k.1 k.2 g₀, hA _ _ f₀⟩) hc
  let ψ₀ : LinearMap.range ιv →ₗ[ℂ] R.Pi :=
    (LinearMap.ker ιv).liftQ κv hker ∘ₗ ιv.quotKerEquivRange.symm.toLinearMap
  have hψ₀ : ∀ c, ψ₀ ⟨ιv c, LinearMap.mem_range_self ιv c⟩ = κv c := by
    intro c
    change (LinearMap.ker ιv).liftQ κv hker (ιv.quotKerEquivRange.symm ⟨ιv c, LinearMap.mem_range_self ιv c⟩) = κv c
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend ψ₀
  have hψι : ∀ c, ψ (ιv c) = κv c := fun c => by
    have := LinearMap.congr_fun hψ ⟨ιv c, LinearMap.mem_range_self ιv c⟩
    rw [LinearMap.comp_apply, hψ₀] at this
    exact this
  have hψv : ∀ i, ψ (v i) = u i := fun i => by
    have := hψι (Finsupp.single i 1)
    simpa only [ιv, κv, Finsupp.linearCombination_single, one_smul] using this
  have hTv : ∀ k₁ (hk₁ : k₁ ∈ KInf σ G₁.W B.emb) (i : {k : UA σ G₁.W.J // k ∈ KInf σ G₁.W B.emb}),
      T₁ k₁ hk₁ (v i) = v ⟨k₁ * i.1, kInf_mul hk₁ i.2⟩ := by
    intro k₁ hk₁ i
    have c1 := acts_mul hw₁ i.1 k₁ (hA₁ i.1 i.2 g₀) (hA₁ k₁ hk₁ (A₁ i.1 i.2 g₀))
    have e := (hL₁ _ _ _).2.2.2.1 _ c1 (hA₁ (k₁ * i.1) (kInf_mul hk₁ i.2) g₀)
    change T₁ k₁ hk₁ (R₁.p (A₁ i.1 i.2 g₀)) = R₁.p (A₁ (k₁ * i.1) (kInf_mul hk₁ i.2) g₀)
    rw [← hT₁ k₁ hk₁ _ (hpol₁ _ _ _ hg₀P), e]
  have hv1 : v ⟨1, h1₁⟩ = R₁.p g₀ := by
    have e := (hL₁ _ _ _).2.2.2.1 _ (hA₁ 1 h1₁ g₀) (acts_one om₁ g₀)
    change R₁.p (A₁ 1 h1₁ g₀) = _
    rw [e]
  have hg₀V : R₁.p g₀ ∈ lowPartInf B G₁.M R₁.p := ⟨g₀, hg₀, rfl⟩

  have hspan : Submodule.span ℂ (Set.range v) = lowPartInf B G₁.M R₁.p := by
    have hle : Submodule.span ℂ (Set.range v) ≤ lowPartInf B G₁.M R₁.p := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      exact (GlobalTheory.T.low_part_compact_stable hKP F E σ B a b G₁ X om₁ om₁' R₁ Rf₁ hm₁).1 i.1 i.2 g₀ hg₀P _ (hA₁ i.1 i.2 g₀) hg₀V
    refine (GlobalTheory.T.lowPart_invariant_submodule_dense hKP F E σ B a b G₁ X om₁ om₁' R₁ Rf₁ hm₁ _ hle ?_).resolve_left ?_
    · intro k₁ hk₁ g hg g₁ hact hmem
      have e : g₁ = A₁ k₁ hk₁ g := (hL₁ _ _ _).2.2.2.1 _ hact (hA₁ k₁ hk₁ g)
      rw [e, hT₁ k₁ hk₁ g hg]
      have hst : Submodule.span ℂ (Set.range v) ≤ (Submodule.span ℂ (Set.range v)).comap (T₁ k₁ hk₁) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨i, rfl⟩
        change T₁ k₁ hk₁ (v i) ∈ Submodule.span ℂ (Set.range v)
        rw [hTv]
        exact Submodule.subset_span ⟨_, rfl⟩
      exact hst hmem
    · intro hbot
      apply hv0
      rw [← hv1]
      exact (Submodule.eq_bot_iff _).1 hbot _ (Submodule.subset_span ⟨_, rfl⟩)
  have hu1 : u ⟨1, h1₁⟩ = R.p f₀ :=
    hswap (Lf 1 h1₁) 1 1 1 g₀ g₀ _ f₀ ⟨hLfK 1 h1₁, h1₁, hLfL 1 h1₁, acts_one om₁ g₀, hA _ _ f₀⟩
      ⟨h1, h1₁, isLevi_one H', acts_one om₁ g₀, acts_one om f₀⟩ rfl
  refine ⟨ψ, ⟨R₁.p g₀, hg₀V, by rw [← hv1, hψv, hu1]; exact hw0⟩, ?_, ?_⟩
  · have hst := GlobalTheory.TwPartStabBeta.kStabL_twPart_beta hKP F E σ B a b G G₁ H H' hcfg X om om' R Rf om₁ om₁' R₁ Rf₁ hm hm₁
    have hle : Submodule.span ℂ (Set.range v) ≤
        (twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p)).comap ψ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      change ψ (v i) ∈ twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p)
      rw [hψv]
      exact hst _ (hLfK i.1 i.2) i.1 i.2 (hLfL i.1 i.2) f₀ hf₀ _ (hA _ _ f₀) hwT
    intro y hy
    rw [← hspan] at hy
    exact hle hy
  · intro k hk k₁ hk₁ hL' g hg g₁ hact hgV f hf f₁ hactf hψg
    have e₁ : g₁ = A₁ k₁ hk₁ g := (hL₁ _ _ _).2.2.2.1 _ hact (hA₁ k₁ hk₁ g)
    have e : f₁ = A k hk f := (hL _ _ _).2.2.2.1 _ hactf (hA k hk f)
    rw [e₁, e, hT₁ k₁ hk₁ g hg, hT k hk f hf, ← hψg]
    rw [← hspan] at hgV
    refine LinearMap.eqOn_span' (f := ψ ∘ₗ T₁ k₁ hk₁) (g := T k hk ∘ₗ ψ) ?_ hgV
    rintro _ ⟨i, rfl⟩
    change ψ (T₁ k₁ hk₁ (v i)) = T k hk (ψ (v i))
    rw [hTv, hψv, hψv]
    change R.p (A _ _ f₀) = T k hk (R.p (A _ _ f₀))
    rw [← hT k hk _ (hpol _ _ _ hf₀)]
    exact hswap (Lf (k₁ * i.1) (kInf_mul hk₁ i.2)) (k * Lf i.1 i.2) (k₁ * i.1) (k₁ * i.1) _ _ _ _
      ⟨hLfK _ _, kInf_mul hk₁ i.2, hLfL _ _, hA₁ _ (kInf_mul hk₁ i.2) g₀, hA _ _ f₀⟩
      ⟨kInf_mul hk (hLfK _ _), kInf_mul hk₁ i.2, isLevi_mul hL' (hLfL _ _), hA₁ _ (kInf_mul hk₁ i.2) g₀,
        acts_mul hw _ k (hA _ _ f₀) (hA k hk _)⟩ rfl

end GlobalTheory.BranchMapB
