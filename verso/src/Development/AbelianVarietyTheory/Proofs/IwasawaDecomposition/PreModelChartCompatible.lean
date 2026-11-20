import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSpanOfPluckerProportionalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartGluingStatement

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

/- English proof (translation)
Establish `hc : c = c'`. Establish `h1` using `(pt_str c v hv).symm.trans ((congrArg (· ≫ PSpace.str O N) h).trans (pt_str c' w hw))`. Conclude with `congrArg CommRingCat.Hom.hom (Spec.map_injective h1)`. Substitute `hc` using the available equality. Take `⟨u, hu⟩` from `(pt_eq_pt_iff c hv hw).1 h`.

Use `⟨fun h0 => ?_, u, hu⟩` and prove the remaining obligations. Rewrite `hw` using `[h0]`. Use `bot_ne_top (α := Ideal k) (Eq.trans ?_ hw)` and prove the remaining obligations. Use `(Ideal.span_eq_bot.2 ?_).symm` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`.

Both sides reduce to the same expression.
-/
theorem exists_smul_of_pt_eq {O k : Type} [CommRing O] [Field k] {N : ℕ} {c c' : O →+* k} {v w : Fin (N + 1) → k}
    {hv : Ideal.span (Set.range v) = ⊤} {hw : Ideal.span (Set.range w) = ⊤} (h : pt c v hv = pt c' w hw) :
    w ≠ 0 ∧ ∃ u : k, w = u • v := by
  have hc : c = c' := by
    have h1 := (pt_str c v hv).symm.trans ((congrArg (· ≫ PSpace.str O N) h).trans (pt_str c' w hw))
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  subst hc
  obtain ⟨u, hu⟩ := (pt_eq_pt_iff c hv hw).1 h
  refine ⟨fun h0 => ?_, u, hu⟩
  rw [h0] at hw
  refine bot_ne_top (α := Ideal k) (Eq.trans ?_ hw)
  refine (Ideal.span_eq_bot.2 ?_).symm
  rintro _ ⟨i, rfl⟩
  rfl

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨l, rfl⟩` from `hx`. Use `⟨Pi.single (Fin.castLE h l) 1, fun j hj => Pi.single_eq_of_ne ?_ _, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Conclude with `absurd l.2 (not_lt.2 hj)`. Simplify using `[Pi.single_apply]`. Consider the case `zero => exact ⟨0, fun _ _ => rfl, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, rfl⟩` from `hx`.

Take `⟨b, hb, rfl⟩` from `hy`. Conclude with `⟨a + b, fun j hj => by simp [ha j hj, hb j hj], by simp [add_smul, Finset.sum_add_distrib]⟩`. Consider the case `smul r x _ hx`. Take `⟨a, ha, rfl⟩` from `hx`. Conclude with `⟨r • a, fun j hj => by simp [ha j hj], by simp [Finset.smul_sum, smul_smul]⟩`.
-/
theorem exists_coeff_of_mem_span_initial {k V : Type} [Field k] [AddCommGroup V] [Module k V] {m n : ℕ} (h : n ≤ m)
    (c : Fin m → V) {v : V} (hv : v ∈ Submodule.span k (Set.range fun l : Fin n => c (Fin.castLE h l))) :
    ∃ cf : Fin m → k, (∀ j : Fin m, n ≤ (j : ℕ) → cf j = 0) ∧ v = ∑ j, cf j • c j := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, rfl⟩ := hx
    refine ⟨Pi.single (Fin.castLE h l) 1, fun j hj => Pi.single_eq_of_ne ?_ _, ?_⟩
    · rintro rfl
      exact absurd l.2 (not_lt.2 hj)
    · simp [Pi.single_apply]
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, fun j hj => by simp [ha j hj, hb j hj], by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul r x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨r • a, fun j hj => by simp [ha j hj], by simp [Finset.smul_sum, smul_smul]⟩

/- English proof (translation)
Introduce `E _ _ _ H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T k _ a a' φ φ' e τ n hn i hi`. Establish `hn' : n ≤ Dw.mult τ`. Rewrite `hn` using `[T.ty]`. Conclude with `Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)`. Establish `hx : spMap (φ.comp (ρ a)) ≫ (aff (ι a)).fromSpec = spMap φ ≫ Z.chart a ≫ Z.π`.

Rewrite using `[spMap_comp, Category.assoc, T.res a]`. Establish `e' : spMap φ ≫ Z.chart a ≫ Z.π = spMap φ' ≫ Z.chart a' ≫ Z.π`. Rewrite using `[← Category.assoc, e, Category.assoc]`. Take `⟨h1, e1⟩` from `GlobalTheory.T.pre_model_chart_gluing E H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T k a (ι a) φ _ hx (stdEn τ n hn')`. Take `⟨h2, e2⟩` from `GlobalTheory.T.pre_model_chart_gluing E H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T k a' (ι a) φ' _ (hx.trans e') (stdEn τ n hn')`.

Establish `e3 : spMap φ ≫ Z.chart a ≫ g (stdEn τ n hn') = spMap φ' ≫ Z.chart a' ≫ g (stdEn τ n hn')`. Rewrite using `[← Category.assoc, e, Category.assoc]`. Take `⟨h0, u, hu⟩` from `exists_smul_of_pt_eq (e1.symm.trans (e3.trans e2))`. Establish `hm` using `GlobalTheory.T.mem_span_of_plucker_proportional k M n (fun l => crd (ι a) k (φ.comp (ρ a)) ((Z.fr a).bc φ τ (Fin.castLE hn' l))) (fun l => crd (ι a) k (φ.comp (ρ a)) ((Z.fr a').bc φ' τ (Fin.castLE hn' l))) u h0 hu ⟨i, hi⟩`. Take `⟨cf, hcf, hs⟩` from `exists_coeff_of_mem_span_initial hn' (fun j => crd (ι a) k (φ.comp (ρ a)) ((Z.fr a).bc φ τ j)) hm`.

Use `⟨cf, hcf, (T.emb.comb_iff (ι a) (φ.comp (ρ a)) hx (fun j => ((T.frame a k φ).1 τ j).1) (e' ▸ ((T.frame a' k φ').1 τ i).1) cf).2 hs⟩` and prove the remaining obligations.
-/
theorem tie_glue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Pre Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M) (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)) (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Comparison₂ Z L aff crd ι ρ g → ∀ (k : Type) [Field k] (a a' : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* k) (φ' : Γ(Z.X, (Z.U a').1) →+* k), spMap φ ≫ Z.chart a = spMap φ' ≫ Z.chart a' → SameFlag Z.ty (Y Z.i).t (spMap φ ≫ Z.chart a ≫ Z.π) ((Z.fr a).bc φ) ((Z.fr a').bc φ') := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T k _ a a' φ φ' e τ n hn i hi
  have hn' : n ≤ Dw.mult τ := by
    rw [T.ty] at hn
    exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
  have hx : spMap (φ.comp (ρ a)) ≫ (aff (ι a)).fromSpec = spMap φ ≫ Z.chart a ≫ Z.π := by
    rw [spMap_comp, Category.assoc, T.res a]
  have e' : spMap φ ≫ Z.chart a ≫ Z.π = spMap φ' ≫ Z.chart a' ≫ Z.π := by
    rw [← Category.assoc, e, Category.assoc]
  obtain ⟨h1, e1⟩ := GlobalTheory.T.pre_model_chart_gluing E H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T k a (ι a) φ _ hx (stdEn τ n hn')
  obtain ⟨h2, e2⟩ := GlobalTheory.T.pre_model_chart_gluing E H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T k a' (ι a) φ' _ (hx.trans e') (stdEn τ n hn')
  have e3 : spMap φ ≫ Z.chart a ≫ g (stdEn τ n hn') = spMap φ' ≫ Z.chart a' ≫ g (stdEn τ n hn') := by
    rw [← Category.assoc, e, Category.assoc]
  obtain ⟨h0, u, hu⟩ := exists_smul_of_pt_eq (e1.symm.trans (e3.trans e2))
  have hm := GlobalTheory.T.mem_span_of_plucker_proportional k M n
    (fun l => crd (ι a) k (φ.comp (ρ a)) ((Z.fr a).bc φ τ (Fin.castLE hn' l)))
    (fun l => crd (ι a) k (φ.comp (ρ a)) ((Z.fr a').bc φ' τ (Fin.castLE hn' l))) u h0 hu ⟨i, hi⟩
  obtain ⟨cf, hcf, hs⟩ := exists_coeff_of_mem_span_initial hn'
    (fun j => crd (ι a) k (φ.comp (ρ a)) ((Z.fr a).bc φ τ j)) hm
  refine ⟨cf, hcf, (T.emb.comb_iff (ι a) (φ.comp (ρ a)) hx (fun j => ((T.frame a k φ).1 τ j).1)
    (e' ▸ ((T.frame a' k φ').1 τ i).1) cf).2 hs⟩

end GlobalTheory.FlagEmb
