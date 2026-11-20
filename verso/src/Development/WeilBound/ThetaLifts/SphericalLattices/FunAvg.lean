import Development.WeilBound.ThetaLifts.SphericalLattices.FunDefs

noncomputable section

namespace PositivityTheory.Sph

section AvgAbs

variable {Γ : Type} [Group Γ]

def avgQ (H : Subgroup Γ) (f : Γ → ℂ) : ℂ := (H.index : ℂ)⁻¹ * ∑ᶠ q : Γ ⧸ H, f (Quotient.out q)

/- English proof (translation)
Take `⟨h, e⟩` from `QuotientGroup.mk_out_eq_mul H g`. Rewrite using `[e, hf g h h.2]`.
-/
theorem out_mk_inv {H : Subgroup Γ} {f : Γ → ℂ} (hf : ∀ x, ∀ h ∈ H, f (x * h) = f x) (g : Γ) :
    f (Quotient.out (g : Γ ⧸ H)) = f g := by
  obtain ⟨h, e⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [e, hf g h h.2]

/- English proof (translation)
Establish `hH0 : H.index ≠ 0` using `ne_zero_of_dvd_ne_zero h0 (Subgroup.index_dvd_of_le hle)`. Establish `hmul` using `Subgroup.relIndex_mul_index hle`. Establish `hR0 : H'.relIndex H ≠ 0` using `fun h => h0 (by rw [← hmul, h, zero_mul])`. Establish `: Finite (Γ ⧸ H')` using `Subgroup.index_ne_zero_iff_finite.1 h0`. Establish `: Finite (Γ ⧸ H)` using `Subgroup.index_ne_zero_iff_finite.1 hH0`.

Establish `: Finite (H ⧸ H'.subgroupOf H)` using `Subgroup.index_ne_zero_iff_finite.1 hR0`. Set `_` to `Fintype.ofFinite (Γ ⧸ H')`. Set `_` to `Fintype.ofFinite (Γ ⧸ H)`. Set `_` to `Fintype.ofFinite (H ⧸ H'.subgroupOf H)`. Establish `hf' : ∀ x, ∀ h ∈ H', f (x * h) = f x` using `fun x h hh => hf x h (hle hh)`.

Establish `hg : ∀ q' : Γ ⧸ H', f (Quotient.out q') = f (Quotient.out ((Subgroup.quotientEquivProdOfLE hle q').1))` using `fun q' => by`. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective q'`. Establish `e : ((Subgroup.quotientEquivProdOfLE hle (g : Γ ⧸ H')).1 : Γ ⧸ H) = (g : Γ ⧸ H)` using `rfl`. Rewrite using `[e, out_mk_inv hf', out_mk_inv hf]`. Establish `hcard : (Fintype.card (H ⧸ H'.subgroupOf H) : ℂ) = (H'.relIndex H : ℂ)`.

Rewrite using `[Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]`. Unfold `avgQ`. Rewrite using `[finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Fintype.sum_equiv (Subgroup.quotientEquivProdOfLE hle) _ (fun p => f (Quotient.out p.1)) hg, Fintype.sum_prod_type]`. Simplify using `only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]`. Rewrite using `[← Finset.mul_sum, ← hmul, Nat.cast_mul]`.

Establish `a : (H'.relIndex H : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hR0`. Establish `b : (H.index : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hH0`. Clear the denominators using the available nonvanishing facts.
-/
theorem avgQ_le {H H' : Subgroup Γ} (hle : H' ≤ H) (h0 : H'.index ≠ 0) {f : Γ → ℂ}
    (hf : ∀ x, ∀ h ∈ H, f (x * h) = f x) : avgQ H' f = avgQ H f := by
  classical
  have hH0 : H.index ≠ 0 := ne_zero_of_dvd_ne_zero h0 (Subgroup.index_dvd_of_le hle)
  have hmul := Subgroup.relIndex_mul_index hle
  have hR0 : H'.relIndex H ≠ 0 := fun h => h0 (by rw [← hmul, h, zero_mul])
  have : Finite (Γ ⧸ H') := Subgroup.index_ne_zero_iff_finite.1 h0
  have : Finite (Γ ⧸ H) := Subgroup.index_ne_zero_iff_finite.1 hH0
  have : Finite (H ⧸ H'.subgroupOf H) := Subgroup.index_ne_zero_iff_finite.1 hR0
  let _ := Fintype.ofFinite (Γ ⧸ H')
  let _ := Fintype.ofFinite (Γ ⧸ H)
  let _ := Fintype.ofFinite (H ⧸ H'.subgroupOf H)
  have hf' : ∀ x, ∀ h ∈ H', f (x * h) = f x := fun x h hh => hf x h (hle hh)
  have hg : ∀ q' : Γ ⧸ H', f (Quotient.out q') = f (Quotient.out ((Subgroup.quotientEquivProdOfLE hle q').1)) := fun q' => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q'
    have e : ((Subgroup.quotientEquivProdOfLE hle (g : Γ ⧸ H')).1 : Γ ⧸ H) = (g : Γ ⧸ H) := rfl
    rw [e, out_mk_inv hf', out_mk_inv hf]
  have hcard : (Fintype.card (H ⧸ H'.subgroupOf H) : ℂ) = (H'.relIndex H : ℂ) := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  unfold avgQ
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    Fintype.sum_equiv (Subgroup.quotientEquivProdOfLE hle) _ (fun p => f (Quotient.out p.1)) hg, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  rw [← Finset.mul_sum, ← hmul, Nat.cast_mul]
  have a : (H'.relIndex H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hR0
  have b : (H.index : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hH0
  field_simp

/- English proof (translation)
Unfold `avgQ`. Use `congr 1`. Establish `e : ∀ q : Γ ⧸ N, f (Quotient.out q * k) = f (Quotient.out (q * (k : Γ ⧸ N)))` using `fun q => by conv_rhs => rw [← QuotientGroup.out_eq' q, ← QuotientGroup.mk_mul]`. Rewrite using `[out_mk_inv hf]`. Simplify using `only [e]`.

Conclude with `finsum_comp_equiv (Equiv.mulRight (k : Γ ⧸ N)) (f := fun q => f (Quotient.out q))`.
-/
theorem avgQ_mul {N : Subgroup Γ} [N.Normal] {f : Γ → ℂ} (hf : ∀ x, ∀ h ∈ N, f (x * h) = f x) (k : Γ) :
    avgQ N (fun x => f (x * k)) = avgQ N f := by
  unfold avgQ
  congr 1
  have e : ∀ q : Γ ⧸ N, f (Quotient.out q * k) = f (Quotient.out (q * (k : Γ ⧸ N))) := fun q => by
    conv_rhs => rw [← QuotientGroup.out_eq' q, ← QuotientGroup.mk_mul]
    rw [out_mk_inv hf]
  simp only [e]
  exact finsum_comp_equiv (Equiv.mulRight (k : Γ ⧸ N)) (f := fun q => f (Quotient.out q))

/- English proof (translation)
Establish `: Finite (Γ ⧸ H)` using `Subgroup.index_ne_zero_iff_finite.1 h0`. Unfold `avgQ`. Rewrite using `[finsum_add_distrib (Set.toFinite _) (Set.toFinite _), mul_add]`.
-/
theorem avgQ_add {H : Subgroup Γ} (h0 : H.index ≠ 0) (f g : Γ → ℂ) :
    avgQ H (fun x => f x + g x) = avgQ H f + avgQ H g := by
  have : Finite (Γ ⧸ H) := Subgroup.index_ne_zero_iff_finite.1 h0
  unfold avgQ
  rw [finsum_add_distrib (Set.toFinite _) (Set.toFinite _), mul_add]

/- English proof (translation)
Unfold `avgQ`. Rewrite using `[← mul_finsum, mul_left_comm]`.
-/
theorem avgQ_smul (H : Subgroup Γ) (c : ℂ) (f : Γ → ℂ) : avgQ H (fun x => c * f x) = c * avgQ H f := by
  unfold avgQ
  rw [← mul_finsum, mul_left_comm]

end AvgAbs

/- English proof (translation)
Introduce `G S _ _ _ K V ω l₀ hV h1 hmul hst`. Set `f : S → K → ℂ` to `fun φ x => l₀ (ω x φ)`. Establish `hfe : ∀ φ (x : K), f φ x = l₀ (ω x φ)` using `fun _ _ => rfl`. Establish `hinvH : ∀ φ ∈ V, ∀ H : Subgroup G, (∀ k ∈ H, ω k φ = φ) → ∀ (x : K), ∀ h ∈ H.subgroupOf K, f φ (x * h) = f φ x` using `fun φ hφ H hH x h hh => by`. Rewrite using `[hfe, hfe, Subgroup.coe_mul, hmul x x.2 h h.2 φ hφ, hH h (Subgroup.mem_subgroupOf.1 hh)]`.

Use `choose Hc hHcK hHc0 hHcfix using hst`. Establish `fin1 : ∀ φ (hφ : φ ∈ V), ((Hc φ hφ).subgroupOf K).FiniteIndex` using `fun φ hφ => ⟨hHc0 φ hφ⟩`. Set `N : ∀ φ, φ ∈ V → Subgroup K` to `fun φ hφ => ((Hc φ hφ).subgroupOf K).normalCore`. Establish `hNn : ∀ φ hφ, (N φ hφ).Normal` using `fun φ hφ => Subgroup.normalCore_normal _`. Establish `hN0 : ∀ φ hφ, (N φ hφ).index ≠ 0` using `fun φ hφ => by haveI := fin1 φ hφ`.

Conclude with `(Subgroup.finiteIndex_normalCore _).index_ne_zero`. Establish `hNinv : ∀ φ hφ, ∀ (x : K), ∀ h ∈ N φ hφ, f φ (x * h) = f φ x` using `fun φ hφ x h hh => hinvH φ hφ _ (hHcfix φ hφ) x h (Subgroup.normalCore_le _ hh)`. Establish `key : ∀ φ (hφ : φ ∈ V) (H' : Subgroup K), H'.index ≠ 0 → (∀ (x : K), ∀ h ∈ H', f φ (x * h) = f φ x) → avgQ H' (f φ) = avgQ (N φ hφ) (f φ)` using `fun φ hφ H' h0 hH' => by`. Establish `hM` using `Subgroup.index_inf_ne_zero h0 (hN0 φ hφ)`. Rewrite using `[← avgQ_le inf_le_left hM hH', avgQ_le inf_le_right hM (hNinv φ hφ)]`.

Set `lamF : S → ℂ` to `fun φ => if hφ : φ ∈ V then avgQ (N φ hφ) (f φ) else 0`. Establish `hlamF : ∀ φ (hφ : φ ∈ V), lamF φ = avgQ (N φ hφ) (f φ)` using `fun φ hφ => dif_pos hφ`. Set `lamV : V →ₗ[ℂ] ℂ` to `{ toFun := fun φ => lamF φ map_add' := fun φ ψ => by`. Establish `hφ` using `φ.2`. Establish `hψ` using `ψ.2`.

Establish `hs` using `V.add_mem hφ hψ`. Establish `h0` using `Subgroup.index_inf_ne_zero (hN0 _ hφ) (hN0 _ hψ)`. Express the relevant statement in the definitionally equal form `lamF (φ.1 + ψ.1) = lamF φ.1 + lamF ψ.1`. Establish `e : f (φ.1 + ψ.1) = fun x => f φ.1 x + f ψ.1 x` using `funext fun x => by rw [hfe, hfe, hfe, map_add, map_add]`. Rewrite using `[hlamF _ hs, hlamF _ hφ, hlamF _ hψ, ← key _ hs _ h0 (fun x h hh => by`.

Rewrite using `[e]`. Conclude with `congrArg₂ (· + ·) (hNinv _ hφ x h hh.1) (hNinv _ hψ x h hh.2)),`. Use the proof step `← key _ hφ _ h0 (fun x h hh => hNinv _ hφ x h hh.1), ← key _ hψ _ h0 (fun x h hh => hNinv _ hψ x h hh.2), e,`. Use `avgQ_add h0]`. Use the proof step `map_smul' := fun c φ => by`.

Establish `hφ` using `φ.2`. Establish `hs` using `V.smul_mem c hφ`. Express the relevant statement in the definitionally equal form `lamF (c • φ.1) = c • lamF φ.1`. Establish `e : f (c • φ.1) = fun x => c * f φ.1 x` using `funext fun x => by rw [hfe, hfe, map_smul, map_smul, smul_eq_mul]`. Rewrite using `[hlamF _ hs, hlamF _ hφ, ← key _ hs _ (hN0 _ hφ) (fun x h hh => by rw [e]; exact congrArg (c * ·) (hNinv _ hφ x h hh)), e, avgQ_smul, smul_eq_mul] }`.

Take `⟨π, hπ⟩` from `LinearMap.exists_leftInverse_of_injective V.subtype V.ker_subtype`. Establish `hπ' : ∀ φ (hφ : φ ∈ V), π φ = ⟨φ, hφ⟩` using `fun φ hφ => LinearMap.congr_fun hπ ⟨φ, hφ⟩`. Establish `hlam : ∀ φ (hφ : φ ∈ V), (lamV ∘ₗ π) φ = avgQ (N φ hφ) (f φ)` using `fun φ hφ => by`. Rewrite using `[LinearMap.comp_apply, hπ' φ hφ]`. Conclude with `hlamF φ hφ`.

Use `⟨lamV ∘ₗ π, fun k hk φ hφ => ?_, fun φ hφ H hHK hH0 hH => ?_⟩` and prove the remaining obligations. Establish `hψ` using `hV k hk φ hφ haveI := hNn φ hφ haveI := hNn _ hψ`. Establish `h0` using `Subgroup.index_inf_ne_zero (hN0 _ hφ) (hN0 _ hψ)`. Establish `e : f (ω k φ) = fun x => f φ (x * ⟨k, hk⟩)` using `funext fun x => by`. Rewrite using `[hfe, hfe, Subgroup.coe_mul, hmul x x.2 k hk φ hφ]`.

Rewrite using `[hlam _ hψ, hlam _ hφ, ← key _ hψ _ h0 (fun x h hh => hNinv _ hψ x h hh.2), ← key _ hφ _ h0 (fun x h hh => hNinv _ hφ x h hh.1), e]`. Conclude with `avgQ_mul (N := N φ hφ ⊓ N (ω k φ) hψ) (fun x h hh => hNinv _ hφ x h hh.1) _`. Rewrite using `[hlam φ hφ, ← key φ hφ (H.subgroupOf K) hH0 (hinvH φ hφ H hH)]`. Both sides reduce to the same expression.
-/
theorem avgSt : AvgSt := by
  classical
  intro G S _ _ _ K V ω l₀ hV h1 hmul hst
  let f : S → K → ℂ := fun φ x => l₀ (ω x φ)
  have hfe : ∀ φ (x : K), f φ x = l₀ (ω x φ) := fun _ _ => rfl
  have hinvH : ∀ φ ∈ V, ∀ H : Subgroup G, (∀ k ∈ H, ω k φ = φ) → ∀ (x : K), ∀ h ∈ H.subgroupOf K, f φ (x * h) = f φ x :=
    fun φ hφ H hH x h hh => by
      rw [hfe, hfe, Subgroup.coe_mul, hmul x x.2 h h.2 φ hφ, hH h (Subgroup.mem_subgroupOf.1 hh)]
  choose Hc hHcK hHc0 hHcfix using hst
  have fin1 : ∀ φ (hφ : φ ∈ V), ((Hc φ hφ).subgroupOf K).FiniteIndex := fun φ hφ => ⟨hHc0 φ hφ⟩
  let N : ∀ φ, φ ∈ V → Subgroup K := fun φ hφ => ((Hc φ hφ).subgroupOf K).normalCore
  have hNn : ∀ φ hφ, (N φ hφ).Normal := fun φ hφ => Subgroup.normalCore_normal _
  have hN0 : ∀ φ hφ, (N φ hφ).index ≠ 0 := fun φ hφ => by
    haveI := fin1 φ hφ
    exact (Subgroup.finiteIndex_normalCore _).index_ne_zero
  have hNinv : ∀ φ hφ, ∀ (x : K), ∀ h ∈ N φ hφ, f φ (x * h) = f φ x := fun φ hφ x h hh =>
    hinvH φ hφ _ (hHcfix φ hφ) x h (Subgroup.normalCore_le _ hh)

  have key : ∀ φ (hφ : φ ∈ V) (H' : Subgroup K), H'.index ≠ 0 → (∀ (x : K), ∀ h ∈ H', f φ (x * h) = f φ x) →
      avgQ H' (f φ) = avgQ (N φ hφ) (f φ) := fun φ hφ H' h0 hH' => by
    have hM := Subgroup.index_inf_ne_zero h0 (hN0 φ hφ)
    rw [← avgQ_le inf_le_left hM hH', avgQ_le inf_le_right hM (hNinv φ hφ)]
  let lamF : S → ℂ := fun φ => if hφ : φ ∈ V then avgQ (N φ hφ) (f φ) else 0
  have hlamF : ∀ φ (hφ : φ ∈ V), lamF φ = avgQ (N φ hφ) (f φ) := fun φ hφ => dif_pos hφ
  let lamV : V →ₗ[ℂ] ℂ :=
    { toFun := fun φ => lamF φ
      map_add' := fun φ ψ => by
        have hφ := φ.2
        have hψ := ψ.2
        have hs := V.add_mem hφ hψ
        have h0 := Subgroup.index_inf_ne_zero (hN0 _ hφ) (hN0 _ hψ)
        change lamF (φ.1 + ψ.1) = lamF φ.1 + lamF ψ.1
        have e : f (φ.1 + ψ.1) = fun x => f φ.1 x + f ψ.1 x := funext fun x => by rw [hfe, hfe, hfe, map_add, map_add]
        rw [hlamF _ hs, hlamF _ hφ, hlamF _ hψ, ← key _ hs _ h0 (fun x h hh => by
            rw [e]; exact congrArg₂ (· + ·) (hNinv _ hφ x h hh.1) (hNinv _ hψ x h hh.2)),
          ← key _ hφ _ h0 (fun x h hh => hNinv _ hφ x h hh.1), ← key _ hψ _ h0 (fun x h hh => hNinv _ hψ x h hh.2), e,
          avgQ_add h0]
      map_smul' := fun c φ => by
        have hφ := φ.2
        have hs := V.smul_mem c hφ
        change lamF (c • φ.1) = c • lamF φ.1
        have e : f (c • φ.1) = fun x => c * f φ.1 x := funext fun x => by rw [hfe, hfe, map_smul, map_smul, smul_eq_mul]
        rw [hlamF _ hs, hlamF _ hφ, ← key _ hs _ (hN0 _ hφ) (fun x h hh => by rw [e]; exact congrArg (c * ·) (hNinv _ hφ x h hh)),
          e, avgQ_smul, smul_eq_mul] }
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective V.subtype V.ker_subtype
  have hπ' : ∀ φ (hφ : φ ∈ V), π φ = ⟨φ, hφ⟩ := fun φ hφ => LinearMap.congr_fun hπ ⟨φ, hφ⟩
  have hlam : ∀ φ (hφ : φ ∈ V), (lamV ∘ₗ π) φ = avgQ (N φ hφ) (f φ) := fun φ hφ => by
    rw [LinearMap.comp_apply, hπ' φ hφ]
    exact hlamF φ hφ
  refine ⟨lamV ∘ₗ π, fun k hk φ hφ => ?_, fun φ hφ H hHK hH0 hH => ?_⟩
  · have hψ := hV k hk φ hφ
    haveI := hNn φ hφ
    haveI := hNn _ hψ
    have h0 := Subgroup.index_inf_ne_zero (hN0 _ hφ) (hN0 _ hψ)
    have e : f (ω k φ) = fun x => f φ (x * ⟨k, hk⟩) := funext fun x => by
      rw [hfe, hfe, Subgroup.coe_mul, hmul x x.2 k hk φ hφ]
    rw [hlam _ hψ, hlam _ hφ, ← key _ hψ _ h0 (fun x h hh => hNinv _ hψ x h hh.2),
      ← key _ hφ _ h0 (fun x h hh => hNinv _ hφ x h hh.1), e]
    exact avgQ_mul (N := N φ hφ ⊓ N (ω k φ) hψ) (fun x h hh => hNinv _ hφ x h hh.1) _
  · rw [hlam φ hφ, ← key φ hφ (H.subgroupOf K) hH0 (hinvH φ hφ H hH)]
    rfl

end PositivityTheory.Sph

end
