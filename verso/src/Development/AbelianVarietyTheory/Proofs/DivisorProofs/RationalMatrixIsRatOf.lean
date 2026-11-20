import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasWitness
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MarkedLatticeIsometryDoubleCosetMove
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv.LatMove

/- English proof (translation)
Take `⟨δ₀, -, he⟩` from `hδ`. Establish `he' : ∀ i j, (matHom V δ).1 i j = (1 : AF D.host.F) ⊗ₜ δ₀.1 i j` using `fun i j => (congrArg (fun x : GL (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) he).symm`. Use extensionality with `i j`. Establish `h₀ : archM V θ δ i j = τ (δ₀.1 i j)`. Express the relevant statement in the definitionally equal form `θ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V δ).1 i j)) = _`.

Rewrite using `[he', Algebra.TensorProduct.map_tmul, map_one]`. Conclude with `hθ.1 _`. Establish `e : δ₀.1 i j = δ₁.1 i j` using `τ.injective (by rw [← h₀, h₁]; rfl)`. Conclude with `(he' i j).trans (congrArg (fun x => (1 : AF D.host.F) ⊗ₜ[D.host.F] x) e)`.
-/
theorem rational_matrix_isRatOf {D : D7} (V : HSp D) (δ : GA D V) (hδ : δ ∈ GQ V) (τ : D.host.E →+* ℂ)
    (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (hθ : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ)
    (δ₁ : GL (Fin V.rank) D.host.E) (h₁ : archM V θ δ = δ₁.1.map τ) : GlobalTheory.Ker.IsRatOf V δ₁ δ := by
  obtain ⟨δ₀, -, he⟩ := hδ
  have he' : ∀ i j, (matHom V δ).1 i j = (1 : AF D.host.F) ⊗ₜ δ₀.1 i j := fun i j =>
    (congrArg (fun x : GL (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) he).symm
  ext i j
  have h₀ : archM V θ δ i j = τ (δ₀.1 i j) := by
    change θ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V δ).1 i j)) = _
    rw [he', Algebra.TensorProduct.map_tmul, map_one]
    exact hθ.1 _
  have e : δ₀.1 i j = δ₁.1 i j := τ.injective (by rw [← h₀, h₁]; rfl)
  exact (he' i j).trans (congrArg (fun x => (1 : AF D.host.F) ⊗ₜ[D.host.F] x) e)

/- English proof (translation)
Establish `s1 : (τ X.κ0).im < 0` using `X.κ0_sign ⟨τ, h⟩`. Establish `s2 : (τ X'.κ0).im < 0` using `X'.κ0_sign ⟨τ, h'⟩`. Apply the tactic sequence `rcases X.κ0_xi with e | e <;> rcases X'.κ0_xi with e' | e'`. Rewrite using `[e, e', hξ]`. Rewrite `s1` using `[e, hξ]`.

Rewrite `s2` using `[e', map_neg, Complex.neg_im]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `s1` using `[e, hξ, map_neg, Complex.neg_im]`. Rewrite `s2` using `[e']`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[e, e', hξ]`.
-/
theorem kappa_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X X' : Data E r) (τ : E →+* ℂ)
    (h : τ ∈ X.Ψ) (h' : τ ∈ X'.Ψ) (hξ : X.ξ0 = X'.ξ0) : X.κ0 = X'.κ0 := by
  have s1 : (τ X.κ0).im < 0 := X.κ0_sign ⟨τ, h⟩
  have s2 : (τ X'.κ0).im < 0 := X'.κ0_sign ⟨τ, h'⟩
  rcases X.κ0_xi with e | e <;> rcases X'.κ0_xi with e' | e'
  · rw [e, e', hξ]
  · rw [e, hξ] at s1
    rw [e', map_neg, Complex.neg_im] at s2
    linarith
  · rw [e, hξ, map_neg, Complex.neg_im] at s1
    rw [e'] at s2
    linarith
  · rw [e, e', hξ]

/- English proof (translation)
Rewrite using `[smul_neg, ← h]`. Normalize the expressions using the abelian group laws.
-/
theorem flip_congr {A : Type} [AddCommGroup A] {a b y : A} {N : ℕ} (h : a - b = N • y) : b = a + N • (-y) := by
  rw [smul_neg, ← h]
  abel

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D H Dw l Xo c σ W U dict ι x₀ hG _ d hd κ lev hκ hlev h γ γ' hat hat'`. Take `⟨-, hU, -, -, hW, -⟩` from `hG`. Take `⟨⟨hγ, hΛ, hm⟩, hfr⟩` from `hat`. Take `⟨⟨hγ', hΛ', hm'⟩, hfr'⟩` from `hat'`. Establish `hδ : γ' * γ⁻¹ ∈ GQ W` using `mul_mem hγ' (inv_mem hγ)`.

Take `⟨δ, hδu, hδf, hδa⟩` from `GlobalTheory.MarkCoset.rational_matrix W _ hδ`. Establish `hprod : γ' * γ⁻¹ * (γ * h) * κ = γ' * (h * κ)` using `by group`. Establish `hκ1 : latGHat W κ = latGHat W 1`. Unfold `latGHat`. Rewrite using `[hκ.2, (GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.stabLat_one W).2]`.

Establish `hpsi : ∀ k k', (U.X k).Ψ = (U.X k').Ψ` using `fun k k' => Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hU.2.1 k').2 τ).symm`. Choose the witnesses or unpack the hypotheses as in `⟨τ₀, hτ₀⟩ : ∃ τ, τ ∈ (U.X (dict h).1).Ψ := by`. Distinguish the cases in `h0 : D.host.φ₀ ∈ (U.X (dict h).1).Ψ`. Conclude with `⟨_, h0⟩`. Conclude with `⟨_, not_not.1 (mt ((U.X (dict h).1).cmType _).2 h0)⟩`.

Establish `hξ : (U.X (dict h).1).ξ0 = (U.X (dict (h * κ)).1).ξ0` using `(hW _).2.trans (hW _).2.symm`. Establish `hs : SameSp (U.X (dict h).1) (U.X (dict (h * κ)).1)` using `⟨hpsi _ _, (hW _).1.trans (hW _).1.symm, (hU.2.1 _).1.trans (hU.2.1 _).1.symm, hξ, kappa_eq _ _ τ₀ hτ₀ (hpsi _ _ ▸ hτ₀) hξ⟩`. Take `⟨ht1, ht2⟩` from `GlobalTheory.ShortMoveIso.transport (finHom W) (latGHat W) (fun g => (GlobalTheory.MarkCoset.latG_spec D W g).2) l.M (γ' * γ⁻¹) (γ * h) κ hκ1`. Rewrite `ht1`, `ht2` using `[hprod]`. Establish `hmem : ∀ v, v ∈ (U.X (dict h).1).Λ ↔ finVec W v ∈ latGHat W (γ * h)` using `fun v => by`.

Rewrite using `[← (GlobalTheory.MarkCoset.latG_spec D W _).1, ← SetLike.mem_coe, hΛ]`. Conclude with `Set.ext_iff.1 (Set.image_id _) v`. Establish `hmem' : ∀ v, v ∈ (U.X (dict (h * κ)).1).Λ ↔ finVec W v ∈ latGHat W (γ' * (h * κ))` using `fun v => by`. Rewrite using `[← (GlobalTheory.MarkCoset.latG_spec D W _).1, ← SetLike.mem_coe, hΛ']`. Conclude with `Set.ext_iff.1 (Set.image_id _) v`.

Establish `hlat : ∀ v, v ∈ (U.X (dict h).1).Λ ↔ δ.1 *ᵥ v ∈ (U.X (dict (h * κ)).1).Λ` using `fun v => by`. Rewrite using `[hmem, hmem', ht1, hδf]`. Establish `hM0 : l.M ≠ 0` using `by have := l.three_le; omega`. Establish `hG' : (U.X (dict (h * κ)).1).Gm = -W.gram.transpose` using `(hW _).1`. Use `⟨δ, hs, rational_matrix_isRatOf W _ hδ τ₀ _ (hd.1 _ ⟨τ₀, hτ₀⟩) δ (hδa _ _ (hd.1 _ ⟨τ₀, hτ₀⟩)), fun u v => by rw [hG']; exact hδu u v, ?_, ?_, fun a ha => ?_⟩` and prove the remaining obligations.

Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`. Conclude with `(hlat u).1 hu`. Introduce `hv`.

Establish `hri : δ.1 *ᵥ ((δ⁻¹).1 *ᵥ v) = v` using `by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Conclude with `⟨(δ⁻¹).1 *ᵥ v, (hlat _).2 (by rw [hri]; exact hv), hri⟩`. Use function extensionality and compare the values at `τ`. Establish `hτ : τ.1 ∈ (U.X (dict h).1).Ψ` using `by rw [hs.psi]; exact τ.2`. Establish `e1` using `hfr ⟨τ.1, hτ⟩`.

Establish `e2` using `hfr' τ`. Establish `hth` using `hd.1 _ τ`. Rewrite `e1` using `[GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hd.1 _ ⟨τ.1, hτ⟩) hth]`. Establish `hmul : ∀ a b : GA D W, archM W (d.th _ τ) (a * b) = archM W (d.th _ τ) a * archM W (d.th _ τ) b`. Introduce `a b`.

Rewrite using `[archM, archM, archM, map_mul, Units.val_mul, Matrix.map_mul]`. Establish `hone : archM W (d.th _ τ) κ = 1`. Rewrite using `[archM, show infHom W κ = 1 from hκ.1, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite `e2` using `[← hprod, hmul, hmul, hone, Matrix.mul_one, hδa _ _ hth]`. Express the relevant statement in the definitionally equal form `δ.1.map τ.1 * mat (dict h).2 ⟨τ.1, hτ⟩ = mat (dict (h * κ)).2 τ`.

Rewrite using `[e1, e2, ← Matrix.mul_assoc]`. Both sides reduce to the same expression. Take `⟨y, hy, ey⟩` from `hlev a ha`. Take `⟨z, hz, e⟩` from `ht2 (finVec W (d.φ (dict h).1 (d.F.t (d.ik (dict h).1) (lev a)) : Fin W.rank → D.host.E)) (finVec W (d.φ (dict (h * κ)).1 (d.F.t (d.ik (dict (h * κ)).1) a) : Fin W.rank → D.host.E)) _ _ ⟨-y, neg_mem hy, flip_congr ey⟩ (hm _ (GlobalTheory.ShortMoveIso.map_mem_half _ lev a ha)) (hm …`. Take `⟨w, hw, e'⟩` from `GlobalTheory.MarkCoset.finVec_div W l.M hM0 (δ.1 *ᵥ (d.φ (dict h).1 (d.F.t (d.ik (dict h).1) (lev a)) : Fin W.rank → D.host.E) - (d.φ (dict (h * κ)).1 (d.F.t (d.ik (dict (h * κ)).1) a) : Fin W.rank → D.host.E)) z (by`.

Rewrite using `[← e, hδf]`. Use function extensionality and compare the values at `i`. Conclude with `TensorProduct.tmul_sub _ _ _)`. Conclude with `⟨w, (hmem' w).2 (hw ▸ hz), sub_eq_iff_eq_add'.1 e'⟩`.
-/
theorem lattice_move : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (W : HSp D) (U : Unf Xo c σ W.rank) (dict : GA D W → Σ k, Frame (U.X k).Ψ W.rank) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin W.rank) (Fin W.rank) ℂ), GeoSet W U dict x₀ → LatEmb W ι → ∀ d : GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws.DictDat U, d.Is W rfl dict ι x₀ → ∀ (κ : GA D W) (lev : Dw.La →ₗ[𝓞 D.host.E] Dw.La), GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.StabLat W κ → GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.LevAgrees W ι l.M (Mfr l) κ lev → ∀ h γ γ' : GA D W, d.At W rfl dict ι x₀ h γ → d.At W rfl dict ι x₀ (h * κ) γ' → ∃ (ga : GL (Fin W.rank) D.host.E) (hs : SameSp (U.X (dict h).1) (U.X (dict (h * κ)).1)), GlobalTheory.Ker.IsRatOf W ga (γ' * γ⁻¹) ∧ IsUn (U.X (dict (h * κ)).1) ga ∧ mapL ga (U.X (dict h).1).Λ = (U.X (dict (h * κ)).1).Λ ∧ lact ga (castFr hs.psi (dict h).2) = (dict (h * κ)).2 ∧ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ u ∈ (U.X (dict (h * κ)).1).Λ, (ga : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ (d.φ (dict h).1 (d.F.t (d.ik (dict h).1) (lev a)) : Fin W.rank → D.host.E) = (d.φ (dict (h * κ)).1 (d.F.t (d.ik (dict (h * κ)).1) a) : Fin W.rank → D.host.E) + l.M • u := by
  intro D H Dw l Xo c σ W U dict ι x₀ hG _ d hd κ lev hκ hlev h γ γ' hat hat'
  obtain ⟨-, hU, -, -, hW, -⟩ := hG
  obtain ⟨⟨hγ, hΛ, hm⟩, hfr⟩ := hat
  obtain ⟨⟨hγ', hΛ', hm'⟩, hfr'⟩ := hat'
  have hδ : γ' * γ⁻¹ ∈ GQ W := mul_mem hγ' (inv_mem hγ)
  obtain ⟨δ, hδu, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix W _ hδ
  have hprod : γ' * γ⁻¹ * (γ * h) * κ = γ' * (h * κ) := by group
  have hκ1 : latGHat W κ = latGHat W 1 := by
    unfold latGHat
    rw [hκ.2, (GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.stabLat_one W).2]
  have hpsi : ∀ k k', (U.X k).Ψ = (U.X k').Ψ := fun k k' =>
    Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hU.2.1 k').2 τ).symm
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ, τ ∈ (U.X (dict h).1).Ψ := by
    by_cases h0 : D.host.φ₀ ∈ (U.X (dict h).1).Ψ
    · exact ⟨_, h0⟩
    · exact ⟨_, not_not.1 (mt ((U.X (dict h).1).cmType _).2 h0)⟩
  have hξ : (U.X (dict h).1).ξ0 = (U.X (dict (h * κ)).1).ξ0 := (hW _).2.trans (hW _).2.symm
  have hs : SameSp (U.X (dict h).1) (U.X (dict (h * κ)).1) :=
    ⟨hpsi _ _, (hW _).1.trans (hW _).1.symm, (hU.2.1 _).1.trans (hU.2.1 _).1.symm, hξ,
      kappa_eq _ _ τ₀ hτ₀ (hpsi _ _ ▸ hτ₀) hξ⟩
  obtain ⟨ht1, ht2⟩ := GlobalTheory.ShortMoveIso.transport (finHom W) (latGHat W)
    (fun g => (GlobalTheory.MarkCoset.latG_spec D W g).2) l.M (γ' * γ⁻¹) (γ * h) κ hκ1
  rw [hprod] at ht1 ht2
  have hmem : ∀ v, v ∈ (U.X (dict h).1).Λ ↔ finVec W v ∈ latGHat W (γ * h) := fun v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D W _).1, ← SetLike.mem_coe, hΛ]
    exact Set.ext_iff.1 (Set.image_id _) v
  have hmem' : ∀ v, v ∈ (U.X (dict (h * κ)).1).Λ ↔ finVec W v ∈ latGHat W (γ' * (h * κ)) := fun v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D W _).1, ← SetLike.mem_coe, hΛ']
    exact Set.ext_iff.1 (Set.image_id _) v
  have hlat : ∀ v, v ∈ (U.X (dict h).1).Λ ↔ δ.1 *ᵥ v ∈ (U.X (dict (h * κ)).1).Λ := fun v => by
    rw [hmem, hmem', ht1, hδf]
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hG' : (U.X (dict (h * κ)).1).Gm = -W.gram.transpose := (hW _).1
  refine ⟨δ, hs, rational_matrix_isRatOf W _ hδ τ₀ _ (hd.1 _ ⟨τ₀, hτ₀⟩) δ (hδa _ _ (hd.1 _ ⟨τ₀, hτ₀⟩)),
    fun u v => by rw [hG']; exact hδu u v, ?_, ?_, fun a ha => ?_⟩
  · ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (hlat u).1 hu
    · intro hv
      have hri : δ.1 *ᵥ ((δ⁻¹).1 *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      exact ⟨(δ⁻¹).1 *ᵥ v, (hlat _).2 (by rw [hri]; exact hv), hri⟩
  · funext τ
    have hτ : τ.1 ∈ (U.X (dict h).1).Ψ := by rw [hs.psi]; exact τ.2
    have e1 := hfr ⟨τ.1, hτ⟩
    have e2 := hfr' τ
    have hth := hd.1 _ τ
    rw [GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hd.1 _ ⟨τ.1, hτ⟩) hth] at e1
    have hmul : ∀ a b : GA D W, archM W (d.th _ τ) (a * b) = archM W (d.th _ τ) a * archM W (d.th _ τ) b := by
      intro a b
      rw [archM, archM, archM, map_mul, Units.val_mul, Matrix.map_mul]
    have hone : archM W (d.th _ τ) κ = 1 := by
      rw [archM, show infHom W κ = 1 from hκ.1, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← hprod, hmul, hmul, hone, Matrix.mul_one, hδa _ _ hth] at e2
    change δ.1.map τ.1 * mat (dict h).2 ⟨τ.1, hτ⟩ = mat (dict (h * κ)).2 τ
    rw [e1, e2, ← Matrix.mul_assoc]
    rfl
  · obtain ⟨y, hy, ey⟩ := hlev a ha
    obtain ⟨z, hz, e⟩ := ht2 (finVec W (d.φ (dict h).1 (d.F.t (d.ik (dict h).1) (lev a)) : Fin W.rank → D.host.E))
      (finVec W (d.φ (dict (h * κ)).1 (d.F.t (d.ik (dict (h * κ)).1) a) : Fin W.rank → D.host.E)) _ _
      ⟨-y, neg_mem hy, flip_congr ey⟩
      (hm _ (GlobalTheory.ShortMoveIso.map_mem_half _ lev a ha)) (hm' a ha)
    obtain ⟨w, hw, e'⟩ := GlobalTheory.MarkCoset.finVec_div W l.M hM0
      (δ.1 *ᵥ (d.φ (dict h).1 (d.F.t (d.ik (dict h).1) (lev a)) : Fin W.rank → D.host.E) -
        (d.φ (dict (h * κ)).1 (d.F.t (d.ik (dict (h * κ)).1) a) : Fin W.rank → D.host.E)) z (by
        rw [← e, hδf]
        funext i
        exact TensorProduct.tmul_sub _ _ _)
    exact ⟨w, (hmem' w).2 (hw ▸ hz), sub_eq_iff_eq_add'.1 e'⟩

end GlobalTheory.FrameEquiv.LatMove
