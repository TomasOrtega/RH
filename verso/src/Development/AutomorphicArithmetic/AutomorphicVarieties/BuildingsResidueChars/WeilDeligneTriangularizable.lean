import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AbelianFieldWindowTripleSnoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneTriangularInitialSegment
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneFunctorExactness
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Module
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.Pst.DpstMap UpperTheory.V UpperTheory.V.Af.Wd

/- English proof (translation)
Take `⟨y, hy0, hy⟩` from `finrank_eq_one_iff'.1 h1`. Take `⟨c, hc⟩` from `hy (N y)`. Take `⟨n, hn⟩` from `hN`. Establish `hp : ∀ m : ℕ, (N ^ m) y = c ^ m • y`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih => rw [pow_succ', End.mul_apply, ih, map_smul, ← hc, smul_smul, pow_succ]`. Establish `h2` using `hp n`. Rewrite `h2` using `[hn, LinearMap.zero_apply]`.

Establish `hc0 : c = 0`. Break down `smul_eq_zero.1 h2.symm with h | h` into its components or cases. Conclude with `(pow_eq_zero_iff'.1 h).1`. Conclude with `absurd h hy0`. Use extensionality with `x`.

Take `⟨a, rfl⟩` from `hy x`. Rewrite using `[map_smul, ← hc, hc0]`. Simplify using the standard rewrite rules.
-/
private theorem nil_line {k W : Type} [Field k] [AddCommGroup W] [Module k W] (h1 : finrank k W = 1) {N : End k W}
    (hN : IsNilpotent N) : N = 0 := by
  obtain ⟨y, hy0, hy⟩ := finrank_eq_one_iff'.1 h1
  obtain ⟨c, hc⟩ := hy (N y)
  obtain ⟨n, hn⟩ := hN
  have hp : ∀ m : ℕ, (N ^ m) y = c ^ m • y := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', End.mul_apply, ih, map_smul, ← hc, smul_smul, pow_succ]
  have h2 := hp n
  rw [hn, LinearMap.zero_apply] at h2
  have hc0 : c = 0 := by
    rcases smul_eq_zero.1 h2.symm with h | h
    · exact (pow_eq_zero_iff'.1 h).1
    · exact absurd h hy0
  ext x
  obtain ⟨a, rfl⟩ := hy x
  rw [map_smul, ← hc, hc0]
  simp

/- English proof (translation)
Use `UpperTheory.abelianField_window_triple_snoc k _ _ _ _ n (ops N' R') _ (ops N'' R'') f p hf hp hex h1 ?_ ?_ _ ?_ ?_` and prove the remaining obligations. Introduce and unpack `(_ | σ) x`. Conclude with `hfN x`. Conclude with `hfR σ x`. Introduce and unpack `(_ | σ) x`.

Conclude with `hpN x`. Conclude with `hpR σ x`. Use `hI using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `a i`. Apply the tactic sequence `cases a <;> rfl`.

Introduce and unpack `(_ | σ) y`. Rewrite using `[ops_none, ops_none, nil_line h1 hN]`. Simplify using the standard rewrite rules. Conclude with `hl σ y`.
-/
private theorem snoc_ops {k W' W W'' Γ : Type} [Field k] [AddCommGroup W'] [Module k W'] [AddCommGroup W] [Module k W]
    [AddCommGroup W''] [Module k W''] {n : ℕ} {N' : End k W'} {N : End k W} {N'' : End k W''} {R' : Γ → End k W'}
    {R : Γ → End k W} {R'' : Γ → End k W''} {f : W' →ₗ[k] W} {p : W →ₗ[k] W''} (hf : Function.Injective f)
    (hp : Function.Surjective p) (hex : Function.Exact f p) (h1 : finrank k W'' = 1) (hfN : ∀ x, f (N' x) = N (f x))
    (hfR : ∀ a x, f (R' a x) = R a (f x)) (hpN : ∀ x, p (N x) = N'' (p x)) (hpR : ∀ a x, p (R a x) = R'' a (p x))
    {μ : Γ → Fin (n + 1) → k} (hI : IsTri (ops N' R') (ops 0 fun a i => μ a (Fin.castSucc i))) (hN : IsNilpotent N'')
    (hl : ∀ a y, R'' a y = μ a (Fin.last n) • y) : IsTri (ops N R) (ops 0 μ) := by
  refine UpperTheory.abelianField_window_triple_snoc k _ _ _ _ n (ops N' R') _ (ops N'' R'') f p hf hp hex h1 ?_ ?_ _ ?_ ?_
  · rintro (_ | σ) x
    · exact hfN x
    · exact hfR σ x
  · rintro (_ | σ) x
    · exact hpN x
    · exact hpR σ x
  · convert hI using 1
    funext a i
    cases a <;> rfl
  · rintro (_ | σ) y
    · rw [ops_none, ops_none, nil_line h1 hN]
      simp
    · exact hl σ y

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l _ ι w A h O _ _ _ Bw hj L n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `V _ _ _ _ _ ρ κ μ ⟨b, _⟩ _ hV`. Use `haveI := hV.finite`.

Establish `h0 : finrank ℂ (WDSpace (Loc.PP l) ι ρ) = 0`. Rewrite using `[LetterDim.finrank_wdSpace l _ ι _ L V ρ hV, finrank_eq_card_basis b, Fintype.card_fin]`. Conclude with `⟨finBasisOfFinrankEq ℂ _ h0, fun a => ⟨fun i => i.elim0, fun i => i.elim0⟩⟩`. Consider the case `succ n ih`. Introduce `V _ _ _ _ _ ρ κ μ hT hκ hV`.

Take `⟨S, hS, p, hp, hker, hpT, hT'⟩` from `UpperTheory.weilDeligne_triangular_initial_segment _ _ _ n _ _ hT`. Set `ρ' : Representation ↥L.1 ↥(GK Bw.Kw) ↥S` to `ρ.subrepresentation S fun g x hx => hS g x hx`. Establish `hf : ∀ g v, S.subtype (ρ' g v) = ρ g (S.subtype v)` using `fun _ _ => rfl`. Establish `hpe : ∀ g v, p (ρ g v) = Loc.chRep (κ (Fin.last n)) g (p v)` using `fun g v => hpT g v`. Establish `hex : Function.Exact S.subtype p`.

Rewrite using `[LinearMap.exact_iff, hker, Submodule.range_subtype]`. Take `⟨h', h'', hinj, hsurj, hexW⟩` from `UpperTheory.weil_deligne_functor_exactness l ι Bw.Kw L ↥S V ↥L.1 ρ' ρ (Loc.chRep (κ (Fin.last n))) S.subtype p hf hpe S.subtype_injective hp hex hV`. Use `haveI := hV.finite`. Use `haveI := h'.finite`. Use `haveI := h''.finite`.

Establish `h1 : finrank ℂ (WDSpace (Loc.PP l) ι (Loc.chRep (κ (Fin.last n)))) = 1`. Rewrite using `[LetterDim.finrank_wdSpace l _ ι _ L _ _ h'', finrank_self]`. Establish `hI` using `ih ↥S ρ' (fun i => κ (Fin.castSucc i)) (fun σ i => μ σ (Fin.castSucc i)) hT' (fun i => hκ (Fin.castSucc i)) h'`. Conclude with `snoc_ops hinj hsurj hexW h1 (wdLin_wdN _ ι hf) (wdLin_wdRho _ ι Bw h hj hf) (wdLin_wdN _ ι hpe) (wdLin_wdRho _ ι Bw h hj hpe) hI (isNilpotent_wdN _ ι _) (hκ (Fin.last n) h'')`.
-/
theorem UpperTheory.weilDeligne_triangularizable :
    UpperTheory.V.Af.Wd.WdTri := by
  intro F Ω _ _ _ _ _ l _ ι w A h O _ _ _ Bw hj L n
  induction n with
  | zero =>
    intro V _ _ _ _ _ ρ κ μ ⟨b, _⟩ _ hV
    haveI := hV.finite
    have h0 : finrank ℂ (WDSpace (Loc.PP l) ι ρ) = 0 := by
      rw [LetterDim.finrank_wdSpace l _ ι _ L V ρ hV, finrank_eq_card_basis b, Fintype.card_fin]
    exact ⟨finBasisOfFinrankEq ℂ _ h0, fun a => ⟨fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ n ih =>
    intro V _ _ _ _ _ ρ κ μ hT hκ hV
    obtain ⟨S, hS, p, hp, hker, hpT, hT'⟩ := UpperTheory.weilDeligne_triangular_initial_segment _ _ _ n _ _ hT
    let ρ' : Representation ↥L.1 ↥(GK Bw.Kw) ↥S := ρ.subrepresentation S fun g x hx => hS g x hx
    have hf : ∀ g v, S.subtype (ρ' g v) = ρ g (S.subtype v) := fun _ _ => rfl
    have hpe : ∀ g v, p (ρ g v) = Loc.chRep (κ (Fin.last n)) g (p v) := fun g v => hpT g v
    have hex : Function.Exact S.subtype p := by
      rw [LinearMap.exact_iff, hker, Submodule.range_subtype]
    obtain ⟨h', h'', hinj, hsurj, hexW⟩ := UpperTheory.weil_deligne_functor_exactness l ι Bw.Kw L ↥S V ↥L.1 ρ' ρ (Loc.chRep (κ (Fin.last n)))
      S.subtype p hf hpe S.subtype_injective hp hex hV
    haveI := hV.finite
    haveI := h'.finite
    haveI := h''.finite
    have h1 : finrank ℂ (WDSpace (Loc.PP l) ι (Loc.chRep (κ (Fin.last n)))) = 1 := by
      rw [LetterDim.finrank_wdSpace l _ ι _ L _ _ h'', finrank_self]
    have hI := ih ↥S ρ' (fun i => κ (Fin.castSucc i)) (fun σ i => μ σ (Fin.castSucc i)) hT'
      (fun i => hκ (Fin.castSucc i)) h'
    exact snoc_ops hinj hsurj hexW h1 (wdLin_wdN _ ι hf) (wdLin_wdRho _ ι Bw h hj hf) (wdLin_wdN _ ι hpe)
      (wdLin_wdRho _ ι Bw h hj hpe) hI (isNilpotent_wdN _ ι _) (hκ (Fin.last n) h'')
