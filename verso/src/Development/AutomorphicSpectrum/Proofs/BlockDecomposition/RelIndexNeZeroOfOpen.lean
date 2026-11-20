import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFamInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPairProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisExtra
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedProductEmbeddingsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SlotEmbeddingsExistStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTestFunctionProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SlotLevelSubgroupsExistStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedProductIntegralStatement

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical

namespace GlobalTheory.CompanionTheory.FinActS

attribute [local instance] borelG borelF borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

/- English proof (translation)
Use `haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK`. Use `haveI : Finite (K ⧸ V.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ (hV.preimage continuous_subtype_val)`. Conclude with `Subgroup.index_ne_zero_of_finite`.
-/
theorem relIndex_ne_zero_of_open {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {V K : Subgroup H}
    (hV : IsOpen (V : Set H)) (hK : IsCompact (K : Set H)) : V.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : Finite (K ⧸ V.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ (hV.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

/- English proof (translation)
The claim follows from `Prod.ext (map_mul (finGL E a) _ _) (map_mul (finGL E b) _ _)`.
-/
theorem finH_mul (x y : Hf E a b) : finH (x * y) = finH x * finH y :=
  Prod.ext (map_mul (finGL E a) _ _) (map_mul (finGL E b) _ _)

/- English proof (translation)
The claim follows from `Prod.ext (map_one (finGL E a)) (map_one (finGL E b))`.
-/
theorem finH_one : finH (1 : Hf E a b) = 1 :=
  Prod.ext (map_one (finGL E a)) (map_one (finGL E b))

/- English proof (translation)
Break down `i with w | w` into its components or cases. Express the relevant statement in the definitionally equal form `hint (K2 a b w.1) (fun m => φ₁ w.1 m * pairRt a b w.1 m G z) = hint (K2 a b w.1) fun m => φ₁ w.1 m * G (z * finH (e (.inl w) m))`. Use `congrArg _ (funext fun m => ?_)` and prove the remaining obligations. Rewrite using `[he₁]`. Both sides reduce to the same expression.

Express the relevant statement in the definitionally equal form `hint (K2 a b w.1) (fun m => φ₂ w.1 m * pairRtT a b w.1 m G z) = hint (K2 a b w.1) fun m => φ₂ w.1 m * G (z * finH (e (.inr w) m))`. Use `congrArg _ (funext fun m => ?_)` and prove the remaining obligations. Rewrite using `[he₂]`. Both sides reduce to the same expression.
-/
theorem actS_eq {S : Set (Pl E)} (φ₁ φ₂ : ∀ w : Pl E, LF a b w) (e : ∀ i : Slot S, (GLw a i.pl × GLw b i.pl) →* Hf E a b)
    (he₁ : ∀ (w : {w // w ∈ S}) (m : GLw a w.1 × GLw b w.1), finH (e (.inl w) m) = (embW a w.1 m.1, embW b w.1 m.2))
    (he₂ : ∀ (w : {w // w ∈ S ∧ IsSplitAt w}) (m : GLw a w.1 × GLw b w.1),
      finH (e (.inr w) m) = (embT a w.1 m.1, embT b w.1 m.2))
    (i : Slot S) (G : H E a b → ℂ) (z : H E a b) :
    actS φ₁ φ₂ i G z = hint (K2 a b i.pl) fun m => sf φ₁ φ₂ i m * G (z * finH (e i m)) := by
  rcases i with w | w
  · change hint (K2 a b w.1) (fun m => φ₁ w.1 m * pairRt a b w.1 m G z) = hint (K2 a b w.1) fun m => φ₁ w.1 m * G (z * finH (e (.inl w) m))
    refine congrArg _ (funext fun m => ?_)
    rw [he₁]
    rfl
  · change hint (K2 a b w.1) (fun m => φ₂ w.1 m * pairRtT a b w.1 m G z) = hint (K2 a b w.1) fun m => φ₂ w.1 m * G (z * finH (e (.inr w) m))
    refine congrArg _ (funext fun m => ?_)
    rw [he₂]
    rfl

/- English proof (translation)
Introduce `hInt hSl hConv _ E _ _ _ B S hS φ₁ φ₂ h₁ h₂ G hG l hl hfix x`. Use `haveI := B.hν`. Use `haveI := B.hν'`. Use `haveI : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩`. Take `⟨hmul, hcont, hsep, -, hev, hmem, -⟩` from `hSl E B.a B.b S hS`.

Take `⟨e, hec, hpe, hpe', he₁, he₂⟩` from `GlobalTheory.T.position_embeddings_exist (E := E) B.a B.b hS`. Take `⟨U₀, hU₀, hlev⟩` from `hG`. Take `⟨-, hc⟩` from `hConv E B S hS`. Take `⟨hcs, ⟨U₁, hU₁, hinv⟩, -⟩` from `hc φ₁ φ₂ h₁ h₂`. Take `⟨L, hLo, hLe, hLi, hLc, hLu⟩` from `GlobalTheory.T.position_level_subgroups_exist (S := S) h₁ h₂`.

Set `p : ∀ i : Slot S, Hf E B.a B.b →* GLw B.a i.pl × GLw B.b i.pl` to `fun i => MonoidHom.mk' (i.cp B.a B.b) (hmul i)`. Set `K : Subgroup (Hf E B.a B.b)` to `(Kf E B.a).prod (Kf E B.b)`. Establish `hKo : IsOpen (K : Set (Hf E B.a B.b))`. Rewrite using `[Subgroup.coe_prod]`. Conclude with `GlobalTheory.CompanionTheory.EulerV.isOpen_Kf.prod GlobalTheory.CompanionTheory.EulerV.isOpen_Kf`.

Establish `hKc : IsCompact (K : Set (Hf E B.a B.b))`. Rewrite using `[Subgroup.coe_prod]`. Conclude with `GlobalTheory.CompanionTheory.EulerV.isCompact_Kf.prod GlobalTheory.CompanionTheory.EulerV.isCompact_Kf`. Establish `hKHo : ∀ i : Slot S, IsOpen (K2 B.a B.b i.pl : Set (GLw B.a i.pl × GLw B.b i.pl))` using `fun i => (GlobalTheory.CompanionTheory.FinTestTw.isRestrW B.a B.b).isOpen_K i.pl`. Establish `hKHc : ∀ i : Slot S, IsCompact (K2 B.a B.b i.pl : Set (GLw B.a i.pl × GLw B.b i.pl))` using `fun i => (GlobalTheory.CompanionTheory.FinTestTw.isRestrW B.a B.b).isCompact_K i.pl`.

Take `⟨V₀, hV₀o, hV₀K, hV₀e, hV₀U⟩` from `GlobalTheory.T.restricted_product_embeddings p e K (fun i => K2 B.a B.b i.pl) hcont hec hpe hpe' hsep hmem hKc hKHo U₀ hU₀`. Set `V : ∀ i : Slot S, Subgroup (GLw B.a i.pl × GLw B.b i.pl)` to `fun i => V₀ i ⊓ L i`. Establish `hVo : ∀ i, IsOpen (V i : Set (GLw B.a i.pl × GLw B.b i.pl))` using `fun i => by`. Simplify using `only [V, Subgroup.coe_inf]`. Conclude with `(hV₀o i).inter (hLo i)`.

Set `g : Hf E B.a B.b → ℂ` to `fun h => G (x * finH h)`. Establish `hact` using `actS_eq φ₁ φ₂ e he₁ he₂`. Establish `hcore` using `GlobalTheory.T.restricted_product_integral p e K (fun i => K2 B.a B.b i.pl) V (sf φ₁ φ₂) hpe hpe' hsep hev hmem (fun i => inf_le_left.trans (hV₀K i)) (fun i => relIndex_ne_zero_of_open (hVo i) (hKHc i)) (by filter_upwards [hV₀e, hLe, hLu] with i a₁ a₂ a₃`. Conclude with `⟨by simp only [V, a₁, a₂, inf_idem], a₃⟩)`. Use the proof step `(fun i u hu y => hLi i u hu.2 y)`.

Use the proof step `(fun i => GlobalTheory.TwTrLin.finite_out_support (hVo i) (hLc i))`. Use `g`. Use the proof step `(fun u hu y => by`. Establish `hu₀ : u ∈ U₀` using `hV₀U u fun i => (hu i).1`. Simplify using `only [g]`.

Rewrite using `[finH_mul, ← mul_assoc]`. Conclude with `hlev u hu₀ _)`. Use `l hl`. Use the proof step `(fun i hi => funext fun y => by`. Establish `h1` using `hact i G (x * finH y)`.

Rewrite `h1` using `[hfix i hi]`. Simplify using `only [g, finH_mul, ← mul_assoc]`. Conclude with `h1.symm)`. Establish `hfold : ∀ (l' : List (Slot S)) (y : Hf E B.a B.b), l'.foldr (fun i g' x => hint (K2 B.a B.b i.pl) fun m => sf φ₁ φ₂ i m * g' (x * e i m)) g y = l'.foldr (fun i g' => actS φ₁ φ₂ i g') G (x * finH y)`. Introduce `l'`.

Proceed by induction on `l' with`. Consider the case `nil => intro y`. Both sides reduce to the same expression. Consider the case `cons i l' ih`. Introduce `y`.

Simplify using `only [List.foldr_cons]`. Rewrite using `[hact]`. Use `congrArg _ (funext fun m => ?_)` and prove the remaining obligations. Rewrite using `[ih, finH_mul, mul_assoc]`. Establish `hint₁` using `hInt (Hf E B.a B.b) B.ν K (U₀ ⊓ U₁) (fun h => finFn S φ₁ φ₂ h * g h) hKo hKc (by rw [Subgroup.coe_inf]; exact hU₀.inter hU₁) hcs.mul_right (fun u hu y => by`.

Establish `e1` using `(hinv u hu.2 y).2`. Simplify using `only [g]`. Rewrite using `[e1, finH_mul, ← mul_assoc, hlev u hu.1])`. Use `inferInstance`. Establish `hF : (fun h => finFn S φ₁ φ₂ h * g h) = fun h => (∏ᶠ i : Slot S, sf φ₁ φ₂ i (p i h)) * g h`.

Use function extensionality and compare the values at `fun h => by rw [GlobalTheory.T.finite_test_function_product h₁ h₂]; rfl`. Establish `hfin` using `hfold l 1`. Rewrite `hfin` using `[finH_one, mul_one]`. Rewrite using `[← hfin, ← hcore, ← hF]`. Conclude with `hint₁`.
-/
theorem finActOf : FinActOf := by
  intro hInt hSl hConv _ E _ _ _ B S hS φ₁ φ₂ h₁ h₂ G hG l hl hfix x
  haveI := B.hν
  haveI := B.hν'
  haveI : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  obtain ⟨hmul, hcont, hsep, -, hev, hmem, -⟩ := hSl E B.a B.b S hS
  obtain ⟨e, hec, hpe, hpe', he₁, he₂⟩ := GlobalTheory.T.position_embeddings_exist (E := E) B.a B.b hS
  obtain ⟨U₀, hU₀, hlev⟩ := hG
  obtain ⟨-, hc⟩ := hConv E B S hS
  obtain ⟨hcs, ⟨U₁, hU₁, hinv⟩, -⟩ := hc φ₁ φ₂ h₁ h₂
  obtain ⟨L, hLo, hLe, hLi, hLc, hLu⟩ := GlobalTheory.T.position_level_subgroups_exist (S := S) h₁ h₂
  let p : ∀ i : Slot S, Hf E B.a B.b →* GLw B.a i.pl × GLw B.b i.pl := fun i => MonoidHom.mk' (i.cp B.a B.b) (hmul i)
  let K : Subgroup (Hf E B.a B.b) := (Kf E B.a).prod (Kf E B.b)
  have hKo : IsOpen (K : Set (Hf E B.a B.b)) := by
    rw [Subgroup.coe_prod]
    exact GlobalTheory.CompanionTheory.EulerV.isOpen_Kf.prod GlobalTheory.CompanionTheory.EulerV.isOpen_Kf
  have hKc : IsCompact (K : Set (Hf E B.a B.b)) := by
    rw [Subgroup.coe_prod]
    exact GlobalTheory.CompanionTheory.EulerV.isCompact_Kf.prod GlobalTheory.CompanionTheory.EulerV.isCompact_Kf
  have hKHo : ∀ i : Slot S, IsOpen (K2 B.a B.b i.pl : Set (GLw B.a i.pl × GLw B.b i.pl)) := fun i =>
    (GlobalTheory.CompanionTheory.FinTestTw.isRestrW B.a B.b).isOpen_K i.pl
  have hKHc : ∀ i : Slot S, IsCompact (K2 B.a B.b i.pl : Set (GLw B.a i.pl × GLw B.b i.pl)) := fun i =>
    (GlobalTheory.CompanionTheory.FinTestTw.isRestrW B.a B.b).isCompact_K i.pl
  obtain ⟨V₀, hV₀o, hV₀K, hV₀e, hV₀U⟩ := GlobalTheory.T.restricted_product_embeddings p e K (fun i => K2 B.a B.b i.pl) hcont hec hpe hpe' hsep hmem hKc hKHo U₀ hU₀
  let V : ∀ i : Slot S, Subgroup (GLw B.a i.pl × GLw B.b i.pl) := fun i => V₀ i ⊓ L i
  have hVo : ∀ i, IsOpen (V i : Set (GLw B.a i.pl × GLw B.b i.pl)) := fun i => by
    simp only [V, Subgroup.coe_inf]
    exact (hV₀o i).inter (hLo i)
  let g : Hf E B.a B.b → ℂ := fun h => G (x * finH h)
  have hact := actS_eq φ₁ φ₂ e he₁ he₂
  have hcore := GlobalTheory.T.restricted_product_integral p e K (fun i => K2 B.a B.b i.pl) V (sf φ₁ φ₂) hpe hpe' hsep hev hmem
    (fun i => inf_le_left.trans (hV₀K i)) (fun i => relIndex_ne_zero_of_open (hVo i) (hKHc i))
    (by
      filter_upwards [hV₀e, hLe, hLu] with i a₁ a₂ a₃
      exact ⟨by simp only [V, a₁, a₂, inf_idem], a₃⟩)
    (fun i u hu y => hLi i u hu.2 y)
    (fun i => GlobalTheory.TwTrLin.finite_out_support (hVo i) (hLc i))
    g
    (fun u hu y => by
      have hu₀ : u ∈ U₀ := hV₀U u fun i => (hu i).1
      simp only [g]
      rw [finH_mul, ← mul_assoc]
      exact hlev u hu₀ _)
    l hl
    (fun i hi => funext fun y => by
      have h1 := hact i G (x * finH y)
      rw [hfix i hi] at h1
      simp only [g, finH_mul, ← mul_assoc]
      exact h1.symm)
  have hfold : ∀ (l' : List (Slot S)) (y : Hf E B.a B.b),
      l'.foldr (fun i g' x => hint (K2 B.a B.b i.pl) fun m => sf φ₁ φ₂ i m * g' (x * e i m)) g y =
        l'.foldr (fun i g' => actS φ₁ φ₂ i g') G (x * finH y) := by
    intro l'
    induction l' with
    | nil => intro y; rfl
    | cons i l' ih =>
      intro y
      simp only [List.foldr_cons]
      rw [hact]
      refine congrArg _ (funext fun m => ?_)
      rw [ih, finH_mul, mul_assoc]
  have hint₁ := hInt (Hf E B.a B.b) B.ν K (U₀ ⊓ U₁) (fun h => finFn S φ₁ φ₂ h * g h) hKo hKc
    (by rw [Subgroup.coe_inf]; exact hU₀.inter hU₁) hcs.mul_right
    (fun u hu y => by
      have e1 := (hinv u hu.2 y).2
      simp only [g]
      rw [e1, finH_mul, ← mul_assoc, hlev u hu.1])
    inferInstance
  have hF : (fun h => finFn S φ₁ φ₂ h * g h) = fun h => (∏ᶠ i : Slot S, sf φ₁ φ₂ i (p i h)) * g h :=
    funext fun h => by rw [GlobalTheory.T.finite_test_function_product h₁ h₂]; rfl
  have hfin := hfold l 1
  rw [finH_one, mul_one] at hfin
  rw [← hfin, ← hcore, ← hF]
  exact hint₁

end GlobalTheory.CompanionTheory.FinActS

end
