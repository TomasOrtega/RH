import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.RelPrim
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.DEquiv

open UpperTheory.V.Cj.A

/- English proof (translation)
Introduce `Γ V S I _ _ _ _ _ d G hY r hr C hC q k u hu hcl hvan`. Establish `hex : ∀ y : List I, y.length = k + 1 → ∃ η : G.Om q, G.dOm q η = u y ∧ ∀ s, ∀ p ∈ {p | ∀ i ∈ y, p ∈ C i s}, (η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p = 0`. Introduce `y hy`. Choose the witnesses or unpack the hypotheses as in `⟨i0, t, rfl⟩ : ∃ i t, y = i :: t := by`. Consider the cases of `y with`.

Consider the case `nil => simp at hy`. Consider the case `cons i t => exact ⟨i, t, rfl⟩`. Use `relPrim Γ V S d G hY (fun s => {p | ∀ i ∈ i0 :: t, p ∈ C i s}) (fun s => ⟨?_, ?_⟩) q (u (i0 :: t)) (hcl _ hy) ?_` and prove the remaining obligations. Introduce `a ha b hb t1 t2 h1 h2 h i hi`. Conclude with `hC.convex i s (ha i hi) (hb i hi) h1 h2 h`.

Introduce `p hp`. Conclude with `hC.sub i0 s (hp i0 List.mem_cons_self)`. Introduce `s p hp`. Conclude with `hvan _ hy s p (Set.mem_univ _) hp`. Use `choose η hη using hex`.

Establish `hηc : ∀ (y y' : List I) (h : y.length = k + 1) (h' : y'.length = k + 1), y = y' → η y h = η y' h'`. Introduce and unpack `y _ h h' rfl`. Both sides reduce to the same expression. Set `g : List I → Γ` to `fun x => (x.head?.map r).getD 1`. Establish `hg : ∀ (γ : Γ) (x : List I), x ≠ [] → g (x.map (γ • ·)) = γ * g x`.

Introduce `γ x hx`. Consider the cases of `x with`. Consider the case `nil => exact absurd rfl hx`. Consider the case `cons i t => simp [g, hr]`. Establish `hlen : ∀ x : List I, (x.map ((g x)⁻¹ • ·)).length = x.length` using `fun x => List.length_map ..`.

Use `⟨fun x => if h : x.length = k + 1 then G.act q (g x) (η (x.map ((g x)⁻¹ • ·)) ((hlen x).trans h)) else 0, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `γ x hx`. Establish `hx' : (x.map (γ • ·)).length = k + 1` using `by simpa using hx`. Establish `hne : x ≠ []`. Introduce and unpack `rfl`.

Simplify using `at hx`. Simplify using `only [dif_pos hx, dif_pos hx']`. Establish `hn : (x.map (γ • ·)).map ((g (x.map (γ • ·)))⁻¹ • ·) = x.map ((g x)⁻¹ • ·)`. Rewrite using `[hg γ x hne, List.map_map]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Simplify using `[smul_smul]`. Rewrite using `[hηc _ _ _ ((hlen x).trans hx) hn, hg γ x hne, map_mul]`. Both sides reduce to the same expression. Introduce `x hx`.

Simplify using `only [dif_pos hx]`. Rewrite using `[UpperTheory.V.Lit.Dr.dEquiv Γ V S d G q, (hη _ _).1, ← hu (g x) _ ((hlen x).trans hx)]`. Use `congr 1`. Simplify using `[List.map_map, Function.comp_def, smul_smul]`. Introduce `x hx s p _ hp`.

Simplify using `only [dif_pos hx]`. Establish `hp' : G.ρ (g x)⁻¹ p ∈ {p | ∀ i ∈ x.map ((g x)⁻¹ • ·), p ∈ C i ((G.σ (g x)⁻¹) s)}`. Introduce `i hi`. Take `⟨j, hj, rfl⟩` from `List.mem_map.1 hi`. Conclude with `(hC.equiv _ j s p).2 (hp j hj)`.

Use extensionality with `v`. Rewrite using `[UpperTheory.V.Lit.Dr.Geo.act_apply, (hη _ _).2 _ _ hp']`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.Cj.A.fwdStep :
    FwdStep := by
  intro Γ V S I _ _ _ _ _ d G hY r hr C hC q k u hu hcl hvan
  classical
  have hex : ∀ y : List I, y.length = k + 1 → ∃ η : G.Om q, G.dOm q η = u y ∧
      ∀ s, ∀ p ∈ {p | ∀ i ∈ y, p ∈ C i s}, (η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p = 0 := by
    intro y hy
    obtain ⟨i0, t, rfl⟩ : ∃ i t, y = i :: t := by
      cases y with
      | nil => simp at hy
      | cons i t => exact ⟨i, t, rfl⟩
    refine relPrim Γ V S d G hY (fun s => {p | ∀ i ∈ i0 :: t, p ∈ C i s}) (fun s => ⟨?_, ?_⟩) q
      (u (i0 :: t)) (hcl _ hy) ?_
    · intro a ha b hb t1 t2 h1 h2 h i hi
      exact hC.convex i s (ha i hi) (hb i hi) h1 h2 h
    · intro p hp
      exact hC.sub i0 s (hp i0 List.mem_cons_self)
    · intro s p hp
      exact hvan _ hy s p (Set.mem_univ _) hp
  choose η hη using hex
  have hηc : ∀ (y y' : List I) (h : y.length = k + 1) (h' : y'.length = k + 1), y = y' → η y h = η y' h' := by
    rintro y _ h h' rfl
    rfl
  let g : List I → Γ := fun x => (x.head?.map r).getD 1
  have hg : ∀ (γ : Γ) (x : List I), x ≠ [] → g (x.map (γ • ·)) = γ * g x := by
    intro γ x hx
    cases x with
    | nil => exact absurd rfl hx
    | cons i t => simp [g, hr]
  have hlen : ∀ x : List I, (x.map ((g x)⁻¹ • ·)).length = x.length := fun x => List.length_map ..
  refine ⟨fun x => if h : x.length = k + 1 then
      G.act q (g x) (η (x.map ((g x)⁻¹ • ·)) ((hlen x).trans h)) else 0, ?_, ?_, ?_⟩
  · intro γ x hx
    have hx' : (x.map (γ • ·)).length = k + 1 := by simpa using hx
    have hne : x ≠ [] := by
      rintro rfl
      simp at hx
    simp only [dif_pos hx, dif_pos hx']
    have hn : (x.map (γ • ·)).map ((g (x.map (γ • ·)))⁻¹ • ·) = x.map ((g x)⁻¹ • ·) := by
      rw [hg γ x hne, List.map_map]
      congr 1
      funext i
      simp [smul_smul]
    rw [hηc _ _ _ ((hlen x).trans hx) hn, hg γ x hne, map_mul]
    rfl
  · intro x hx
    simp only [dif_pos hx]
    rw [UpperTheory.V.Lit.Dr.dEquiv Γ V S d G q, (hη _ _).1, ← hu (g x) _ ((hlen x).trans hx)]
    congr 1
    simp [List.map_map, Function.comp_def, smul_smul]
  · intro x hx s p _ hp
    simp only [dif_pos hx]
    have hp' : G.ρ (g x)⁻¹ p ∈ {p | ∀ i ∈ x.map ((g x)⁻¹ • ·), p ∈ C i ((G.σ (g x)⁻¹) s)} := by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
      exact (hC.equiv _ j s p).2 (hp j hj)
    ext v
    rw [UpperTheory.V.Lit.Dr.Geo.act_apply, (hη _ _).2 _ _ hp']
    simp
