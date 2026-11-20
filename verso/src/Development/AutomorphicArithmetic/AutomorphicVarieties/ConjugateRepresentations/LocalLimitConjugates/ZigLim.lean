import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.PoinOp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.HdHd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.InclFacts

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ} {G : Dr.Geo Γ V S d} {q : ℕ}

/- English proof (translation)
Introduce `s K hK hc`. Use `(h s K hK hc).add (h' s K hK hc)` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `this`.
-/
private theorem fLim_add {w w' : ℕ → G.Om q} (h : FLim G w) (h' : FLim G w') : FLim G fun j => w j + w' j := by
  intro s K hK hc
  have := (h s K hK hc).add (h' s K hK hc)
  rw [add_zero] at this
  exact this

/- English proof (translation)
Introduce `s K hK hKc`. Establish `h1` using `(uniformContinuous_id.const_smul n).comp_tendstoUniformlyOn (h s K hK hKc)`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k x`. Simplify using the standard rewrite rules.

Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules.
-/
private theorem fLim_zsmul (n : ℤ) {w : ℕ → G.Om q} (h : FLim G w) : FLim G fun j => n • w j := by
  intro s K hK hKc
  have h1 := (uniformContinuous_id.const_smul n).comp_tendstoUniformlyOn (h s K hK hKc)
  convert h1 using 1
  · funext k x
    simp
  · funext x
    simp

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty`. Introduce `s K _ _`. Simplify using `only [Finset.sum_empty, ZeroMemClass.coe_zero, Pi.zero_apply]`. Conclude with `Metric.tendstoUniformlyOn_iff.2 fun ε hε => Filter.Eventually.of_forall fun _ x _ => by simpa using hε`.

Consider the case `insert i T hi ih`. Establish `hsum` using `fLim_add (h i (Finset.mem_insert_self i T)) (ih fun i' hi' => h i' (Finset.mem_insert_of_mem hi'))`. Simplify `hsum` using `[Finset.sum_insert hi]`.
-/
private theorem fLim_sum {ι : Type} (T : Finset ι) {w : ι → ℕ → G.Om q} (h : ∀ i ∈ T, FLim G (w i)) :
    FLim G fun j => ∑ i ∈ T, w i j := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro s K _ _
    simp only [Finset.sum_empty, ZeroMemClass.coe_zero, Pi.zero_apply]
    exact Metric.tendstoUniformlyOn_iff.2 fun ε hε =>
      Filter.Eventually.of_forall fun _ x _ => by simpa using hε
  | insert i T hi ih =>
    have hsum := fLim_add (h i (Finset.mem_insert_self i T))
      (ih fun i' hi' => h i' (Finset.mem_insert_of_mem hi'))
    simpa [Finset.sum_insert hi] using hsum

end

/- English proof (translation)
Introduce `Γ V S _ _ _ _ d G hconv hne`. Take `⟨p, hp⟩` from `hne`. Establish `hincl` using `inclFacts Γ V S d G hconv ⟨p, hp⟩`. Establish `main : ∀ (q k : ℕ) (u : ℕ → List Γ → G.Om q), (∀ j, HCoc (G.act q) k (u j)) → (∀ j (x : List Γ), x.length = k + 1 → G.dOm q (u j x) = 0) → (∀ x : List Γ, x.length = k + 1 → FLim G fun j => u j x) → ∃ c : ℕ → List Γ → S → Fin d → ℂ, (∀ j, Zig G q k (u j) (c j)) ∧ ∀ x : List Γ, x.l …`. Introduce `q`.

Proceed by induction on `q with`. Consider the case `zero`. Introduce `k u _ hcl hlim`. Establish `hex : ∀ j (x : List Γ), x.length = k + 1 → ∃ f, G.incl f = u j x` using `fun j x hx => (hincl.2.2 (u j x)).mp (hcl j x hx)`. Use `choose f hf using hex`.

Use `⟨fun j x => if h : x.length = k + 1 then f j x h else 0, ?_, ?_⟩` and prove the remaining obligations. Introduce `j x hx show u j x = G.incl (if h : x.length = k + 1 then f j x h else 0)`. Rewrite using `[dif_pos hx, hf j x hx]`. Introduce `x hx s`. Establish `hx' : x.length = k + 1` using `by simpa using hx`.

Establish `ht` using `(hlim x hx' s {p} (Set.singleton_subset_iff.2 hp) isCompact_singleton).tendsto_at (Set.mem_singleton p)`. Establish `hc` using `((continuous_eval_const (fun _ : Fin 0 => (0 : V))).tendsto _).comp ht`. Establish `heq : ∀ j, ((u j x : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s p) (fun _ => 0) = f j x hx' s`. Introduce `j`. Rewrite using `[← hf j x hx']`.

Simplify using `[Dr.Geo.incl, Set.indicator_of_mem hp]`. Simplify using `only [dif_pos hx']`. Establish `hfun : (fun j => f j x hx' s) = fun j => ((u j x : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s p) (fun _ => 0)`. Use function extensionality and compare the values at `fun j => (heq j).symm`. Rewrite using `[hfun]`.

Simplify using `at hc`. Conclude with `hc`. Consider the case `succ q ih`. Introduce `k u hcoc hcl hlim`. Take `⟨K, hK1, hK2, hK3⟩` from `poinOp Γ V S d G hconv q`.

Establish `hpt : ∀ x : List Γ, G.ρ (x.headD 1) p ∈ G.Y` using `fun x => G.maps _ p hp`. Establish `hbeq : ∀ j, HEquiv (G.act q) k (fun x => K (G.ρ (x.headD 1) p) (u j x))`. Introduce `j γ x hx`. Establish `hne : x ≠ []`. Introduce and unpack `rfl`.

Simplify using `at hx`. Take `⟨y, ys, rfl⟩` from `List.exists_cons_of_ne_nil hne`. Establish `hu` using `(hcoc j).1 γ (y :: ys) hx`. Simplify using `only [List.map_cons] at hu`. Simplify using `only [List.map_cons, List.headD_cons, map_mul]`.

Rewrite using `[hu, hK2 γ _ (G.maps y p hp)]`. Both sides reduce to the same expression. Establish `hlen : ∀ (x : List Γ) i, x.length = k + 1 + 1 → i ∈ Finset.range x.length → (x.eraseIdx i).length = k + 1`. Introduce `x i hx hi`. Rewrite using `[List.length_eraseIdx_of_lt (Finset.mem_range.1 hi)]`.

Use linear arithmetic over natural numbers and integers. Establish `hcl' : ∀ j (x : List Γ), x.length = k + 1 + 1 → G.dOm q (hd (fun x => K (G.ρ (x.headD 1) p) (u j x)) x) = 0`. Introduce `j x hx`. Establish `h0` using `(hcoc j).2 x hx`. Simplify using `only [hd, map_sum, map_zsmul] at h0 ⊢`.

Rewrite using `[← h0]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[hK1 _ (hpt _) _ (hcl j _ (hlen x i hx hi))]`. Establish `hlim' : ∀ x : List Γ, x.length = k + 1 + 1 → FLim G fun j => hd (fun x => K (G.ρ (x.headD 1) p) (u j x)) x`. Introduce `x hx`.

Simplify using `only [hd]`. Apply `fLim_sum` to reduce the goal to its premises. Introduce `i hi`. Apply `fLim_zsmul` to reduce the goal to its premises. Conclude with `hK3 _ (hpt _) _ (hlim _ (hlen x i hx hi))`.

Take `⟨c, hc1, hc2⟩` from `ih (k + 1) (fun j => hd (fun x => K (G.ρ (x.headD 1) p) (u j x))) (fun j => hdHd Γ (G.Om q) (G.act q) k _ (hbeq j)) hcl' hlim'`. Use `⟨c, fun j => ⟨_, hbeq j, fun x hx => hK1 _ (hpt _) _ (hcl j x hx), hc1 j⟩, ?_⟩` and prove the remaining obligations. Introduce `x hx s`. Conclude with `hc2 x (by omega) s`. Conclude with `main`.
-/
theorem UpperTheory.V.Cj.H.zigLim :
    UpperTheory.V.Cj.H.ZigLim := by
  intro Γ V S _ _ _ _ d G hconv hne
  obtain ⟨p, hp⟩ := hne
  have hincl := inclFacts Γ V S d G hconv ⟨p, hp⟩
  have main : ∀ (q k : ℕ) (u : ℕ → List Γ → G.Om q), (∀ j, HCoc (G.act q) k (u j)) →
      (∀ j (x : List Γ), x.length = k + 1 → G.dOm q (u j x) = 0) →
      (∀ x : List Γ, x.length = k + 1 → FLim G fun j => u j x) →
      ∃ c : ℕ → List Γ → S → Fin d → ℂ, (∀ j, Zig G q k (u j) (c j)) ∧
        ∀ x : List Γ, x.length = k + q + 1 → ∀ s, Tendsto (fun j => c j x s) atTop (𝓝 0) := by
    intro q
    induction q with
    | zero =>
      intro k u _ hcl hlim
      classical
      have hex : ∀ j (x : List Γ), x.length = k + 1 → ∃ f, G.incl f = u j x :=
        fun j x hx => (hincl.2.2 (u j x)).mp (hcl j x hx)
      choose f hf using hex
      refine ⟨fun j x => if h : x.length = k + 1 then f j x h else 0, ?_, ?_⟩
      · intro j x hx
        show u j x = G.incl (if h : x.length = k + 1 then f j x h else 0)
        rw [dif_pos hx, hf j x hx]
      · intro x hx s
        have hx' : x.length = k + 1 := by simpa using hx
        have ht := (hlim x hx' s {p} (Set.singleton_subset_iff.2 hp)
          isCompact_singleton).tendsto_at (Set.mem_singleton p)
        have hc := ((continuous_eval_const (fun _ : Fin 0 => (0 : V))).tendsto _).comp ht
        have heq : ∀ j, ((u j x : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s p) (fun _ => 0) =
            f j x hx' s := by
          intro j
          rw [← hf j x hx']
          simp [Dr.Geo.incl, Set.indicator_of_mem hp]
        simp only [dif_pos hx']
        have hfun : (fun j => f j x hx' s) =
            fun j => ((u j x : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s p) (fun _ => 0) :=
          funext fun j => (heq j).symm
        rw [hfun]
        simp at hc
        exact hc
    | succ q ih =>
      intro k u hcoc hcl hlim
      obtain ⟨K, hK1, hK2, hK3⟩ := poinOp Γ V S d G hconv q
      have hpt : ∀ x : List Γ, G.ρ (x.headD 1) p ∈ G.Y := fun x => G.maps _ p hp
      have hbeq : ∀ j, HEquiv (G.act q) k (fun x => K (G.ρ (x.headD 1) p) (u j x)) := by
        intro j γ x hx
        have hne : x ≠ [] := by
          rintro rfl
          simp at hx
        obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hne
        have hu := (hcoc j).1 γ (y :: ys) hx
        simp only [List.map_cons] at hu
        simp only [List.map_cons, List.headD_cons, map_mul]
        rw [hu, hK2 γ _ (G.maps y p hp)]
        rfl
      have hlen : ∀ (x : List Γ) i, x.length = k + 1 + 1 → i ∈ Finset.range x.length →
          (x.eraseIdx i).length = k + 1 := by
        intro x i hx hi
        rw [List.length_eraseIdx_of_lt (Finset.mem_range.1 hi)]
        omega
      have hcl' : ∀ j (x : List Γ), x.length = k + 1 + 1 →
          G.dOm q (hd (fun x => K (G.ρ (x.headD 1) p) (u j x)) x) = 0 := by
        intro j x hx
        have h0 := (hcoc j).2 x hx
        simp only [hd, map_sum, map_zsmul] at h0 ⊢
        rw [← h0]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hK1 _ (hpt _) _ (hcl j _ (hlen x i hx hi))]
      have hlim' : ∀ x : List Γ, x.length = k + 1 + 1 →
          FLim G fun j => hd (fun x => K (G.ρ (x.headD 1) p) (u j x)) x := by
        intro x hx
        simp only [hd]
        apply fLim_sum
        intro i hi
        apply fLim_zsmul
        exact hK3 _ (hpt _) _ (hlim _ (hlen x i hx hi))
      obtain ⟨c, hc1, hc2⟩ := ih (k + 1) (fun j => hd (fun x => K (G.ρ (x.headD 1) p) (u j x)))
        (fun j => hdHd Γ (G.Om q) (G.act q) k _ (hbeq j)) hcl' hlim'
      refine ⟨c, fun j => ⟨_, hbeq j, fun x hx => hK1 _ (hpt _) _ (hcl j x hx), hc1 j⟩, ?_⟩
      intro x hx s
      exact hc2 x (by omega) s
  exact main
