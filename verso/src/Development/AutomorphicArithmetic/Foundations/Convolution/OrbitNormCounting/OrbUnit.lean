import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.NormCount

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

/- English proof (translation)
Establish `htop : rStab (fun _ : H => c) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `k _ x`. Both sides reduce to the same expression. Unfold `avg`.

Rewrite using `[htop, Subgroup.index_top, Nat.cast_one, inv_one, one_mul]`. Rewrite using `[finsum_eq_single (fun _ => c) ((1 : H) : H ⧸ (⊤ : Subgroup H))]`. Introduce `x hx`. Conclude with `absurd (QuotientGroup.subsingleton_quotient_top.elim x _) hx`.
-/
private theorem avg_const' {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have htop : rStab (fun _ : H => c) = ⊤ := by
    rw [eq_top_iff]
    intro k _ x
    rfl
  unfold avg
  rw [htop, Subgroup.index_top, Nat.cast_one, inv_one, one_mul]
  rw [finsum_eq_single (fun _ => c) ((1 : H) : H ⧸ (⊤ : Subgroup H))]
  intro x hx
  exact absurd (QuotientGroup.subsingleton_quotient_top.elim x _) hx

/- English proof (translation)
Unfold `cptPart at hc ⊢`. Proceed by induction on `hc using Subgroup.closure_induction with`. Consider the case `mem x hx`. Apply `Subgroup.subset_closure` to reduce the goal to its premises. Use `⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hx.1) ht, ?_⟩` and prove the remaining obligations.

Set `e : G ≃ₜ G` to `(Homeomorph.mulLeft t⁻¹).trans (Homeomorph.mulRight t)`. Establish `he : ∀ y, e y = t⁻¹ * y * t` using `fun y => rfl`. Establish `hz : ∀ n : ℤ, (t⁻¹ * x * t) ^ n = t⁻¹ * x ^ n * t`. Introduce `n`. Simplify using `using (conj_zpow (a := t⁻¹) (b := x) (i := n))`.

Establish `himg : (Subgroup.zpowers (t⁻¹ * x * t) : Set G) = e '' (Subgroup.zpowers x : Set G)`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, rfl⟩`. Conclude with `⟨x ^ n, ⟨n, rfl⟩, (hz n).symm⟩`.

Introduce and unpack `⟨_, ⟨n, rfl⟩, rfl⟩`. Conclude with `⟨n, hz n⟩`. Rewrite using `[himg, ← e.image_closure]`. Conclude with `hx.2.image e.continuous`. Consider the case `one => simp`.

Consider the case `mul x y _ _ hx hy`. Establish `: t⁻¹ * (x * y) * t = (t⁻¹ * x * t) * (t⁻¹ * y * t)` using `by group`. Rewrite using `[this]`. Conclude with `Subgroup.mul_mem _ hx hy`. Consider the case `inv x _ hx`.

Establish `: t⁻¹ * x⁻¹ * t = (t⁻¹ * x * t)⁻¹` using `by group`. Rewrite using `[this]`. Conclude with `Subgroup.inv_mem _ hx`.
-/
private theorem cptPart_conj {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (T : Subgroup G) {t c : G} (ht : t ∈ T) (hc : c ∈ cptPart T) : t⁻¹ * c * t ∈ cptPart T := by
  unfold cptPart at hc ⊢
  induction hc using Subgroup.closure_induction with
  | mem x hx =>
    apply Subgroup.subset_closure
    refine ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hx.1) ht, ?_⟩
    let e : G ≃ₜ G := (Homeomorph.mulLeft t⁻¹).trans (Homeomorph.mulRight t)
    have he : ∀ y, e y = t⁻¹ * y * t := fun y => rfl
    have hz : ∀ n : ℤ, (t⁻¹ * x * t) ^ n = t⁻¹ * x ^ n * t := by
      intro n
      simpa using (conj_zpow (a := t⁻¹) (b := x) (i := n))
    have himg : (Subgroup.zpowers (t⁻¹ * x * t) : Set G) = e '' (Subgroup.zpowers x : Set G) := by
      ext y
      constructor
      · rintro ⟨n, rfl⟩
        exact ⟨x ^ n, ⟨n, rfl⟩, (hz n).symm⟩
      · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, hz n⟩
    rw [himg, ← e.image_closure]
    exact hx.2.image e.continuous
  | one => simp
  | mul x y _ _ hx hy =>
    have : t⁻¹ * (x * y) * t = (t⁻¹ * x * t) * (t⁻¹ * y * t) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : t⁻¹ * x⁻¹ * t = (t⁻¹ * x * t)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

/- English proof (translation)
Introduce `G _ _ _ θ K δ hθ hδ horb hcpt`. Unfold `twOrb`. Rewrite using `[finsum_eq_single _ (DoubleCoset.mk (twCent θ δ) K 1)]`. Take `⟨t, k, ht, hk, hx⟩` from `DoubleCoset.mk_out_eq_mul (twCent θ δ) K (1 : G)`. Generalize the expression as in `hxx : Quotient.out (DoubleCoset.mk (twCent θ δ) K 1) = x at hx ⊢`.

Rewrite `hx` using `[mul_one]`. Establish `ht' : t * δ = δ * θ t` using `ht`. Establish `h1 : (twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ δ)) = 1`. Rewrite using `[Subgroup.relIndex_eq_one]`. Introduce `c hc`.

Establish `hc'` using `cptPart_conj _ ht hc`. Rewrite `hc`, `hc'` using `[hcpt]`. Use `⟨hc.1, k⁻¹ * (t⁻¹ * c * t) * k, K.mul_mem (K.mul_mem (K.inv_mem hk) hc'.2) hk, ?_⟩` and prove the remaining obligations. Rewrite using `[hx]`. Simplify using `[mul_assoc]`.

Establish `h2 : (fun k' : K => (K : Set G).indicator (1 : G → ℂ) ((x * k')⁻¹ * δ * θ (x * k'))) = fun _ => 1`. Use function extensionality and compare the values at `k'`. Establish `e : (x * k')⁻¹ * δ * θ (x * k') = (k * k')⁻¹ * δ * θ (k * k')`. Establish `: δ * θ (x * k') = t * δ * θ (k * k')`. Rewrite using `[ht', hx, mul_assoc t k, map_mul θ t, mul_assoc]`.

Rewrite using `[mul_assoc, this, hx]`. Use `group`. Establish `hkk : k * k' ∈ K` using `K.mul_mem hk k'.2`. Rewrite using `[e, Set.indicator_of_mem]`. Both sides reduce to the same expression.

Conclude with `K.mul_mem (K.mul_mem (K.inv_mem hkk) hδ) (hθ _ hkk)`. Rewrite using `[h1, h2, avg_const']`. Simplify using the standard rewrite rules. Introduce `q hq`. Establish `h2 : (fun k' : K => (K : Set G).indicator (1 : G → ℂ) ((Quotient.out q * k')⁻¹ * δ * θ (Quotient.out q * k'))) = fun _ => 0`.

Use function extensionality and compare the values at `k'`. Apply `Set.indicator_of_notMem` to reduce the goal to its premises. Introduce `hy`. Apply `hq` to reduce the goal to its premises. Take `⟨k, hk, e⟩` from `horb _ hy ⟨_, rfl⟩`.

Rewrite using `[← DoubleCoset.out_eq' (twCent θ δ) K q]`. Use `symm`. Rewrite using `[DoubleCoset.eq]`. Use `⟨Quotient.out q * k' * k⁻¹, ?_, k * (k' : G)⁻¹, K.mul_mem hk (K.inv_mem k'.2), ?_⟩` and prove the remaining obligations. Generalize the expression as in `Quotient.out q * (k' : G) = g at e show g * k⁻¹ * δ = δ * θ (g * k⁻¹)`.

Rewrite using `[map_mul, map_inv]`. Combine the equalities or inequalities in the displayed calculation. Use `show Quotient.out q = _ group`. Rewrite using `[h2, avg_const', mul_zero]`.
-/
theorem UpperTheory.ConvolutionTheory.G3.orbUnit :
    UpperTheory.ConvolutionTheory.G3.OrbUnit := by
  intro G _ _ _ θ K δ hθ hδ horb hcpt
  unfold twOrb
  rw [finsum_eq_single _ (DoubleCoset.mk (twCent θ δ) K 1)]
  · obtain ⟨t, k, ht, hk, hx⟩ := DoubleCoset.mk_out_eq_mul (twCent θ δ) K (1 : G)
    generalize hxx : Quotient.out (DoubleCoset.mk (twCent θ δ) K 1) = x at hx ⊢
    rw [mul_one] at hx
    have ht' : t * δ = δ * θ t := ht
    have h1 : (twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ δ)) = 1 := by
      rw [Subgroup.relIndex_eq_one]
      intro c hc
      have hc' := cptPart_conj _ ht hc
      rw [hcpt] at hc hc'
      refine ⟨hc.1, k⁻¹ * (t⁻¹ * c * t) * k, K.mul_mem (K.mul_mem (K.inv_mem hk) hc'.2) hk, ?_⟩
      rw [hx]
      simp [mul_assoc]
    have h2 : (fun k' : K => (K : Set G).indicator (1 : G → ℂ) ((x * k')⁻¹ * δ * θ (x * k'))) = fun _ => 1 := by
      funext k'
      have e : (x * k')⁻¹ * δ * θ (x * k') = (k * k')⁻¹ * δ * θ (k * k') := by
        have : δ * θ (x * k') = t * δ * θ (k * k') := by
          rw [ht', hx, mul_assoc t k, map_mul θ t, mul_assoc]
        rw [mul_assoc, this, hx]
        group
      have hkk : k * k' ∈ K := K.mul_mem hk k'.2
      rw [e, Set.indicator_of_mem]
      · rfl
      · exact K.mul_mem (K.mul_mem (K.inv_mem hkk) hδ) (hθ _ hkk)
    rw [h1, h2, avg_const']
    simp
  · intro q hq
    have h2 : (fun k' : K => (K : Set G).indicator (1 : G → ℂ)
        ((Quotient.out q * k')⁻¹ * δ * θ (Quotient.out q * k'))) = fun _ => 0 := by
      funext k'
      apply Set.indicator_of_notMem
      intro hy
      apply hq
      obtain ⟨k, hk, e⟩ := horb _ hy ⟨_, rfl⟩
      rw [← DoubleCoset.out_eq' (twCent θ δ) K q]
      symm
      rw [DoubleCoset.eq]
      refine ⟨Quotient.out q * k' * k⁻¹, ?_, k * (k' : G)⁻¹, K.mul_mem hk (K.inv_mem k'.2), ?_⟩
      · generalize Quotient.out q * (k' : G) = g at e
        show g * k⁻¹ * δ = δ * θ (g * k⁻¹)
        rw [map_mul, map_inv]
        calc g * k⁻¹ * δ = g * (k⁻¹ * δ * θ k) * (θ k)⁻¹ := by group
          _ = δ * (θ g * (θ k)⁻¹) := by rw [← e]; group
      · show Quotient.out q = _
        group
    rw [h2, avg_const', mul_zero]
