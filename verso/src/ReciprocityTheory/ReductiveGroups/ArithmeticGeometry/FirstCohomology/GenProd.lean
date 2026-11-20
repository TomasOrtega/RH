import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X Y : Scheme.{0}} (L : LB X)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Use `⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, LB.oneGen L, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `(i : PEmpty.{1} → L.ι) (j : PEmpty.{1} → L.ι)`. Establish `h0 : (LB.LinComb L (Y` using `Y) (K := PEmpty) PEmpty.elim PEmpty.elim).g i j = 1 :=`.

Both sides reduce to the same expression. Rewrite using `[h0, one_mul]`. Simplify using `only [LB.oneGen, map_one]`. Introduce `U _ h`. Simplify using the standard rewrite rules.

Introduce `Z r z J _`. Simplify using `[val, LB.oneGen]`. Conclude with `map_one (gm r z _)`. Consider the case `succ n ih`. Take `⟨K', hK', φ', ε', t', ht', hprod, hval⟩` from `ih`.

Use `⟨K' ⊕ K n, inferInstance, Sum.elim φ' (φ n), Sum.elim ε' (ε n), LB.mulGen L φ' ε' (φ n) (ε n) t' (t n), ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen L φ' ε' (φ n) (ε n) t' (t n) ht' (ht n), ?_, ?_⟩` and prove the remaining obligations. Introduce `U _ h`. Simplify using `only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.prod_range_succ, hprod U h]`. Introduce `Z r z J hJ`. Rewrite using `[val_mul, Finset.prod_range_succ, hval Z r z J hJ]`.

Conclude with `hJ`.
-/
theorem exists_gen_prod (K : ℕ → Type) [∀ i, Fintype (K i)] (φ : ∀ i, K i → (Y ⟶ X)) (ε : ∀ i, K i → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) (ht : ∀ i, (t i).IsGen) (n : ℕ) :
    ∃ (K' : Type) (_ : Fintype K') (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (t' : LB.Gen (LB.LinComb L φ' ε')),
      t'.IsGen ∧
      (∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U),
        ∏ k, h (φ' k) ^ ε' k = ∏ i ∈ Finset.range n, ∏ k, h (φ i k) ^ ε i k) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
        val t' r z J = ∏ i ∈ Finset.range n, val (t i) r z J := by
  induction n with
  | zero =>
    refine ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, LB.oneGen L, ?_, ?_, ?_⟩
    · rintro (i : PEmpty.{1} → L.ι) (j : PEmpty.{1} → L.ι)
      have h0 : (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim).g i j = 1 :=
        rfl
      rw [h0, one_mul]
      simp only [LB.oneGen, map_one]
    · intro U _ h
      simp
    · intro Z r z J _
      simp [val, LB.oneGen]
      exact map_one (gm r z _)
  | succ n ih =>
    obtain ⟨K', hK', φ', ε', t', ht', hprod, hval⟩ := ih
    refine ⟨K' ⊕ K n, inferInstance, Sum.elim φ' (φ n), Sum.elim ε' (ε n),
      LB.mulGen L φ' ε' (φ n) (ε n) t' (t n),
      ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen L φ' ε' (φ n) (ε n) t' (t n) ht' (ht n), ?_, ?_⟩
    · intro U _ h
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.prod_range_succ, hprod U h]
    · intro Z r z J hJ
      rw [val_mul, Finset.prod_range_succ, hval Z r z J hJ]
      exact hJ

/- English proof (translation)
Establish `hcov : (⊤ : Y.Opens) ≤ ⨆ c : (Y ⟶ X) → L.ι, LB.wchart L φ (fun k => c (φ k))`. Introduce `y _`. Establish `hc : ∀ ψ : Y ⟶ X, ∃ i, ψ.base y ∈ L.U i`. Introduce `ψ`. Establish `hy : ψ.base y ∈ (⨆ i, L.U i)` using `by rw [hL.cover]; simp`.

Conclude with `TopologicalSpace.Opens.mem_iSup.1 hy`. Use `choose c hc using hc`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨c, Set.mem_iInter.2 fun k => hc (φ k)⟩`. Establish `hcompat : ∀ c c' : (Y ⟶ X) → L.ι, res (inf_le_left : LB.wchart L φ (fun k => c (φ k)) ⊓ LB.wchart L φ (fun k => c' (φ k)) ≤ LB.wchart L φ (fun k => c (φ k))) (t.s (fun k => c (φ k))) = res (inf_le_right : LB.wchart L φ (fun k => c (φ k)) ⊓ LB.wchart L φ (fun k => c' (φ k)) ≤ LB.w …`. Introduce `c c'`.

Establish `hg` using `ht (fun k => c (φ k)) (fun k => c' (φ k))`. Establish `h1 : (LB.LinComb L φ ε).g (fun k => c (φ k)) (fun k => c' (φ k)) = 1`. Use `Eq.trans ?_ (hf (Γ(Y, LB.wchart L φ (fun k => c (φ k)) ⊓ LB.wchart L φ (fun k => c' (φ k)))ˣ) (fun ψ => if hψ : ∃ k, φ k = ψ then res (show LB.wchart L φ (fun k => c (φ k)) ⊓ LB.wchart L φ (fun k => c' (φ k)) ≤ ψ ⁻¹ᵁ (L.U (c ψ) ⊓ L.U (c' ψ)) by` and prove the remaining obligations. Take `⟨k, rfl⟩` from `hψ`. Conclude with `le_inf (inf_le_left.trans (LB.wchart_le L φ _ k)) (inf_le_right.trans (LB.wchart_le L φ _ k)))`.

Use the proof step `(pullU ψ _ (L.g (c ψ) (c' ψ)))`. Use `else 1))`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show _ = (dite _ _ _) ^ ε k`. Rewrite using `[dif_pos (show ∃ k', φ k' = φ k from ⟨k, rfl⟩)]`.

Both sides reduce to the same expression. Rewrite `hg` using `[h1, one_mul]`. Conclude with `hg`. Establish `key` using `TopCat.Sheaf.existsUnique_gluing' Y.sheaf (fun c : (Y ⟶ X) → L.ι => LB.wchart L φ (fun k => c (φ k))) ⊤ (fun _ => homOfLE le_top) hcov`. Take `⟨f, hf1, -⟩` from `key (fun c => (t.s (fun k => c (φ k))).val) (fun c c' => congrArg Units.val (hcompat c c'))`.

Take `⟨g, hg1, -⟩` from `key (fun c => ((t.s (fun k => c (φ k)))⁻¹).val) (fun c c' => congrArg (fun u => (u⁻¹).val) (hcompat c c'))`. Take `⟨e, -, he⟩` from `key (fun _ => 1) (fun c c' => (map_one _).trans (map_one _).symm)`. Establish `hfg : f * g = 1` using `(he (f * g) fun c => by rw [map_mul, hf1 c, hg1 c]; exact (t.s _).mul_inv).trans (he 1 fun c => map_one _).symm`. Set `fU : Γ(Y, ⊤)ˣ` to `Units.mkOfMulEqOne f g hfg`. Take `⟨a, ha⟩` from `hp fU.val`.

Use `⟨a, fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Establish `hmem : r.base z ∈ LB.wchart L φ (fun k => J (r ≫ φ k))` using `Set.mem_iInter.2 fun k => hJ (r ≫ φ k)`. Establish `hres : res (le_top : LB.wchart L φ (fun k => J (r ≫ φ k)) ≤ ⊤) fU = t.s (fun k => J (r ≫ φ k))` using `Units.ext (hf1 (fun ψ => J (r ≫ ψ)))`. Rewrite using `[val_of (t := t) (r := r) (z := z) (J := J) (j := fun k => J (r ≫ φ k)) (h := fun _ => rfl), ← hres, gm_res r z le_top hmem fU, ← gs_unit r z ⊤ (by simp) fU, ← ha]`. Conclude with `gs_pull r p z ⊤ (by simp) a`.
-/
theorem exists_const {S₀ : Scheme.{0}} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (p : Y ⟶ S₀) (hp : Function.Surjective p.appTop.hom) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (hf : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = 1) :
    ∃ a : Γ(S₀, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      (val t r z J).val = gs (r ≫ p) z ⊤ a := by
  classical
  have hcov : (⊤ : Y.Opens) ≤ ⨆ c : (Y ⟶ X) → L.ι, LB.wchart L φ (fun k => c (φ k)) := by
    intro y _
    have hc : ∀ ψ : Y ⟶ X, ∃ i, ψ.base y ∈ L.U i := by
      intro ψ
      have hy : ψ.base y ∈ (⨆ i, L.U i) := by rw [hL.cover]; simp
      exact TopologicalSpace.Opens.mem_iSup.1 hy
    choose c hc using hc
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨c, Set.mem_iInter.2 fun k => hc (φ k)⟩
  have hcompat : ∀ c c' : (Y ⟶ X) → L.ι,
      res (inf_le_left : LB.wchart L φ (fun k => c (φ k)) ⊓ LB.wchart L φ (fun k => c' (φ k)) ≤
        LB.wchart L φ (fun k => c (φ k))) (t.s (fun k => c (φ k))) =
      res (inf_le_right : LB.wchart L φ (fun k => c (φ k)) ⊓ LB.wchart L φ (fun k => c' (φ k)) ≤
        LB.wchart L φ (fun k => c' (φ k))) (t.s (fun k => c' (φ k))) := by
    intro c c'
    have hg := ht (fun k => c (φ k)) (fun k => c' (φ k))
    have h1 : (LB.LinComb L φ ε).g (fun k => c (φ k)) (fun k => c' (φ k)) = 1 := by
      refine Eq.trans ?_ (hf (Γ(Y, LB.wchart L φ (fun k => c (φ k)) ⊓ LB.wchart L φ (fun k => c' (φ k)))ˣ)
        (fun ψ => if hψ : ∃ k, φ k = ψ then
          res (show LB.wchart L φ (fun k => c (φ k)) ⊓ LB.wchart L φ (fun k => c' (φ k)) ≤
              ψ ⁻¹ᵁ (L.U (c ψ) ⊓ L.U (c' ψ)) by
            obtain ⟨k, rfl⟩ := hψ
            exact le_inf (inf_le_left.trans (LB.wchart_le L φ _ k))
              (inf_le_right.trans (LB.wchart_le L φ _ k)))
            (pullU ψ _ (L.g (c ψ) (c' ψ)))
          else 1))
      refine Finset.prod_congr rfl fun k _ => ?_
      show _ = (dite _ _ _) ^ ε k
      rw [dif_pos (show ∃ k', φ k' = φ k from ⟨k, rfl⟩)]
      rfl
    rw [h1, one_mul] at hg
    exact hg
  have key := TopCat.Sheaf.existsUnique_gluing' Y.sheaf
    (fun c : (Y ⟶ X) → L.ι => LB.wchart L φ (fun k => c (φ k))) ⊤ (fun _ => homOfLE le_top) hcov
  obtain ⟨f, hf1, -⟩ := key (fun c => (t.s (fun k => c (φ k))).val)
    (fun c c' => congrArg Units.val (hcompat c c'))
  obtain ⟨g, hg1, -⟩ := key (fun c => ((t.s (fun k => c (φ k)))⁻¹).val)
    (fun c c' => congrArg (fun u => (u⁻¹).val) (hcompat c c'))
  obtain ⟨e, -, he⟩ := key (fun _ => 1) (fun c c' => (map_one _).trans (map_one _).symm)
  have hfg : f * g = 1 :=
    (he (f * g) fun c => by rw [map_mul, hf1 c, hg1 c]; exact (t.s _).mul_inv).trans
      (he 1 fun c => map_one _).symm
  let fU : Γ(Y, ⊤)ˣ := Units.mkOfMulEqOne f g hfg
  obtain ⟨a, ha⟩ := hp fU.val
  refine ⟨a, fun Z r z J hJ => ?_⟩
  have hmem : r.base z ∈ LB.wchart L φ (fun k => J (r ≫ φ k)) :=
    Set.mem_iInter.2 fun k => hJ (r ≫ φ k)
  have hres : res (le_top : LB.wchart L φ (fun k => J (r ≫ φ k)) ≤ ⊤) fU = t.s (fun k => J (r ≫ φ k)) :=
    Units.ext (hf1 (fun ψ => J (r ≫ ψ)))
  rw [val_of (t := t) (r := r) (z := z) (J := J) (j := fun k => J (r ≫ φ k)) (h := fun _ => rfl), ← hres,
    gm_res r z le_top hmem fU, ← gs_unit r z ⊤ (by simp) fU, ← ha]
  exact gs_pull r p z ⊤ (by simp) a

end ReciprocityTheory.ChartRestriction.G.H1
