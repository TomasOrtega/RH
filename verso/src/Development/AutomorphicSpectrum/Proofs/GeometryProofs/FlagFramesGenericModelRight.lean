import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdUpdateDiv
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIsLocalRingIsFractionRingStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingPiecesSmoothStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PieceLocalizationAtElementStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistedFrameInChartStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartFrameMatrixRegularStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameMatricesRegularGenericStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

/- English proof (translation)
Take `⟨U, hU, hm⟩` from `hT.affine c hc`. Establish `hq : ∀ q : Cpt ξ, q.1 ∈ U ↔ InChart ξ x c q` using `fun q => ⟨fun h => ((hm q.1).1 h).2, fun h => (hm q.1).2 ⟨q.2, h⟩⟩`. Use `⟨U, ⟨hU, fun q h => ((hm q).1 h).1, fun a => ?_⟩, hq⟩` and prove the remaining obligations. Use `(hT.ring c hc a).trans (forall_congr' fun q => imp_congr (hq q).symm Iff.rfl)` and prove the remaining obligations.
-/
theorem isPiece_chart {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type} {x : κ → Ω}
    (hT : CoordTie ℤ ξ x) {c : κ} (hc : x c ≠ 0) :
    ∃ U : X.Opens, IsPiece ξ U (chartSub x c) ∧ ∀ q : Cpt ξ, q.1 ∈ U ↔ InChart ξ x c q := by
  obtain ⟨U, hU, hm⟩ := hT.affine c hc
  have hq : ∀ q : Cpt ξ, q.1 ∈ U ↔ InChart ξ x c q := fun q =>
    ⟨fun h => ((hm q.1).1 h).2, fun h => (hm q.1).2 ⟨q.2, h⟩⟩
  refine ⟨U, ⟨hU, fun q h => ((hm q).1 h).1, fun a => ?_⟩, hq⟩
  refine (hT.ring c hc a).trans (forall_congr' fun q => imp_congr (hq q).symm Iff.rfl)

/- English proof (translation)
Rewrite `h` using `[Subsingleton.elim inst (Ring.toIntAlgebra F)]`. Then use the resulting hypothesis.
-/
theorem coordTie_int_inst {X : Scheme.{0}} {F : Type} [Field F] {ξ : Spec (CommRingCat.of F) ⟶ X} {κ : Type} {x : κ → F}
    (inst : Algebra ℤ F) (h : @CoordTie X F _ ℤ _ inst ξ κ x) : @CoordTie X F _ ℤ _ (Ring.toIntAlgebra F) ξ κ x := by
  rwa [Subsingleton.elim inst (Ring.toIntAlgebra F)] at h

/- English proof (translation)
Use `(Subring.closure_le).2 (Set.union_subset (fun y hy => le_locSub R g hy) ?_)` and prove the remaining obligations. Introduce and unpack `_ rfl`. Establish `ha : a ≠ 0` using `left_ne_zero_of_mul (h ▸ hg)`. Establish `hb0 : b ≠ 0` using `right_ne_zero_of_mul (h ▸ hg)`. Establish `e : a⁻¹ = b * g⁻¹` using `by rw [← h]; field_simp`.

Rewrite using `[SetLike.mem_coe, e]`. Conclude with `(locSub R g).mul_mem (le_locSub R g hb) (inv_mem_locSub R g)`.
-/
theorem locSub_le_of_mul {F : Type} [Field F] {R : Subring F} {a b g : F} (hb : b ∈ R) (h : a * b = g) (hg : g ≠ 0) :
    locSub R a ≤ locSub R g := by
  refine (Subring.closure_le).2 (Set.union_subset (fun y hy => le_locSub R g hy) ?_)
  rintro _ rfl
  have ha : a ≠ 0 := left_ne_zero_of_mul (h ▸ hg)
  have hb0 : b ≠ 0 := right_ne_zero_of_mul (h ▸ hg)
  have e : a⁻¹ = b * g⁻¹ := by rw [← h]; field_simp
  rw [SetLike.mem_coe, e]
  exact (locSub R g).mul_mem (le_locSub R g hb) (inv_mem_locSub R g)

/- English proof (translation)
Introduce `X Ω _ ξ E _ _ κ _ x S _ r V L m n φ c X' ξ' f hT hall hVB hTw hc hT' hall' hdom hch`. Establish `hi : Function.Injective (algebraMap Ω (GenField Ω r))` using `(algebraMap Ω (GenField Ω r)).injective`. Use `GlobalTheory.T.dominating_pieces_smooth X X' Ω (GenField Ω r) ξ ξ' f (algebraMap Ω (GenField Ω r)) hT.gen hT'.gen hdom (fun p' => ?_)` and prove the remaining obligations. Set `P' : Cpt ξ'` to `⟨p', hall' p'⟩`. Take `⟨⟨c₀, J⟩, hcJ⟩` from `hT'.cover P'`.

Establish `hy0 : flagCoord κ x φ c (c₀, J) ≠ 0` using `hcJ.1`. Establish `hx0 : x c₀ ≠ 0`. Introduce `h0`. Apply `hy0` to reduce the goal to its premises. Simplify using `[flagCoord, h0]`.

Establish `hover : ∀ Q' : Cpt ξ', InChart ξ' (flagCoord κ x φ c) ((c₀, J) : FlagIx κ n r) Q' → InChart ξ x c₀ ⟨f Q'.1, hall _⟩`. Introduce `Q' hQ`. Use `(hch Q' c₀ (hall _)).2 ⟨by simpa using hx0, fun k => ?_⟩` and prove the remaining obligations. Establish `h` using `hQ.2 ((k, J) : FlagIx κ n r)`. Establish `hpr : (∏ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det) ≠ 0`.

Introduce `h0`. Apply `hy0` to reduce the goal to its premises. Simplify using `[flagCoord, h0]`. Establish `e : flagCoord κ x φ c ((k, J) : FlagIx κ n r) / flagCoord κ x φ c ((c₀, J) : FlagIx κ n r) = algebraMap Ω (GenField Ω r) (x k) / algebraMap Ω (GenField Ω r) (x c₀)`. Simplify using `only [flagCoord]`.

Establish `: algebraMap Ω (GenField Ω r) (x c₀) ≠ 0` using `by simpa using hx0`. Clear the denominators using the available nonvanishing facts. Rewrite `h` using `[e]`. Then use the resulting hypothesis. Set `P : Cpt ξ` to `⟨f p', hall _⟩`. Establish `h2 : InChart ξ x c₀ P` using `hover P' hcJ`.

Establish `hfr` using `fun s => GlobalTheory.T.twisted_frame_in_chart X Ω ξ E κ x (r s) (V s) (L s) (m s) (n s) (φ s) (c s) c₀ P hT hall (hVB s) (hTw s) (hc s) h2`. Use `choose g hgR hgu T M N hT0 hM hN hNM hφ using hfr`. Set `g₀ : Ω` to `∏ s, g s`. Establish `hg₀R : g₀ ∈ chartSub x c₀` using `Subring.prod_mem _ fun s _ => hgR s`. Establish `hg₀0 : g₀ ≠ 0` using `Finset.prod_ne_zero_iff.2 fun s _ => (hgu s).1`.

Establish `hreg : ∀ a ∈ chartSub x c₀, ∀ Q : Cpt ξ, InChart ξ x c₀ Q → a ∈ regAt ξ Q` using `fun a ha Q hQ => (hT.ring c₀ hx0 a).1 ha Q hQ`. Establish `hg₀inv : g₀⁻¹ ∈ regAt ξ P`. Establish `: g₀⁻¹ = ∏ s, (g s)⁻¹` using `by simp [g₀]`. Rewrite using `[this]`. Conclude with `Subring.prod_mem _ fun s _ => (hgu s).2.2`.

Establish `hg₀u : unitAt ξ P g₀` using `⟨hg₀0, hreg _ hg₀R P h2, hg₀inv⟩`. Set `R : Subring Ω` to `locSub (chartSub x c₀) g₀`. Establish `hle : ∀ s, locSub (chartSub x c₀) (g s) ≤ R` using `fun s => locSub_le_of_mul (b := ∏ s' ∈ Finset.univ.erase s, g s') (Subring.prod_mem _ fun s' _ => hgR s') (Finset.mul_prod_erase Finset.univ g (Finset.mem_univ s)) hg₀0`. Establish `hRP : ∀ a ∈ R, a ∈ regAt ξ P`. Establish `: R ≤ regAt ξ P` using `(Subring.closure_le).2 (Set.union_subset (fun y hy => hreg y hy P h2) (by rintro _ rfl; exact hg₀inv))`.

Conclude with `this`. Take `⟨hPh, hdom1, -⟩` from `RegAtDom.regAt_dominates X Ω ξ X' (GenField Ω r) ξ' f _ hdom P'`. Establish `hRO : ∀ a ∈ R, algebraMap Ω (GenField Ω r) a ∈ regAt ξ' P'` using `fun a ha => hdom1 a (hRP a ha)`. Use `haveI : IsLocalRing (regAt ξ' P') := (regAt_isLocalRing_isFractionRing_stalk X' _ ξ' hT'.gen P').1`. Establish `hscale : ∀ (k : κ) (J' : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), _` using `fun k J' => flagCoord_eq (m := m) x hφ k J'`.

Establish `hax : algebraMap Ω (GenField Ω r) (x c₀) ≠ 0` using `by simpa using hx0`. Establish `hprod0` using `hscale c₀ J`. Establish `hβ0 : ∀ q, stepMinor (flagB M T q.1) q.2 (J q) ≠ 0`. Introduce `q h0`. Apply `hy0` to reduce the goal to its premises.

Rewrite using `[hprod0, Finset.prod_eq_zero (Finset.mem_univ q) (by rw [h0, mul_zero]), mul_zero]`. Establish `hβJ : ∀ (q : Σ s, Fin (r s)) (J' : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) ∈ regAt ξ' P'`. Introduce `q J'`. Establish `h` using `hcJ.2 ((c₀, Function.update J q J') : FlagIx κ n r)`. Rewrite `h` using `[hscale c₀ (Function.update J q J'), hprod0, mul_div_mul_left _ _ hax, prod_update_div (β := fun q => Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) (fun q b => (algebraMap Ω (GenField Ω r) (x c₀) ^ m q.1) ^ ((q.2 : ℕ) + 1) * stepMinor (flagB M T q.1) q.2 b) J (fun q => mul_ne_zero (pow_ne_z …`.

Conclude with `h`. Take `⟨t, htR, ht0, htO, htiO, hmap, hsm⟩` from `GlobalTheory.T.frame_matrices_regular_generic Ω S r n R (regAt ξ' P') T M N J hRO hT0 (fun s j l => hle s (hM s j l)) (fun s l j => hle s (hN s l j)) hNM hβ0 hβJ`. Take `⟨hgA, hAeq⟩` from `GlobalTheory.T.chart_frame_matrix_regular Ω E κ x S r n m φ c M T c₀ J g₀ hx0 hg₀R hg₀0 hφ hβ0`. Take `⟨U₀, hU₀, hU₀m⟩` from `isPiece_chart hT hx0`. Take `⟨U₁, hU₁, hU₁m⟩` from `GlobalTheory.T.piece_localization_at_element X Ω ξ U₀ _ g₀ hT.gen hU₀ hg₀R hg₀0`.

Take `⟨W₀, hW₀, hW₀m⟩` from `isPiece_chart (coordTie_int_inst _ hT') hy0`. Establish `hig0 : algebraMap Ω (GenField Ω r) g₀ ≠ 0` using `by simpa using hg₀0`. Take `⟨W₁, hW₁, hW₁m⟩` from `GlobalTheory.T.piece_localization_at_element X' _ ξ' W₀ _ _ hT'.gen hW₀ hgA hig0`. Rewrite `hW₁` using `[hAeq]`. Take `⟨W₂, hW₂, hW₂m⟩` from `GlobalTheory.T.piece_localization_at_element X' _ ξ' W₁ _ t hT'.gen hW₁ htR ht0`.

Use `⟨U₁, W₂, R, _, hmap, hU₁, hW₂, ?_, ?_, hsm⟩` and prove the remaining obligations. Introduce `q' hq'`. Set `Q' : Cpt ξ'` to `⟨q', hall' q'⟩`. Establish `e1` using `((hW₂m Q').1 hq').1`. Take `⟨e2, e3⟩` from `(hW₁m Q').1 e1`.

Establish `e4` using `(hW₀m Q').1 e2`. Establish `e5` using `hover Q' e4`. Take `⟨h', -, hun⟩` from `RegAtDom.regAt_dominates X Ω ξ X' (GenField Ω r) ξ' f _ hdom Q'`. Conclude with `(hU₁m ⟨f q', hall _⟩).2 ⟨(hU₀m _).2 e5, hun hT'.gen g₀ (hreg _ hg₀R _ e5) e3⟩`. Use `(hW₂m P').2 ⟨(hW₁m P').2 ⟨(hW₀m P').2 hcJ, hig0, hRO _ (le_locSub _ _ hg₀R), ?_⟩, ht0, htO, htiO⟩` and prove the remaining obligations.

Rewrite using `[← map_inv₀]`. Conclude with `hRO _ (inv_mem_locSub _ _)`.
-/
theorem flag_smooth : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) [Finite κ] (x : κ → Ω) (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω E) (L : S → Lat ξ E) (m n : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω r)) ⟶ X') (f : X' ⟶ X), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → (∀ s, (L s).IsVB (r s) (V s)) → (∀ s, IsTwistGen ξ x (L s) (m s) (φ s)) → (∀ s, LinearIndependent Ω (c s) ∧ Submodule.span Ω (Set.range (c s)) = V s) → CoordTie ℤ ξ' (flagCoord κ x φ c) → (∀ q : X', genPt ξ' ⤳ q) → Dominates ξ' ξ f (algebraMap Ω (GenField Ω r)) → (∀ (p' : Cpt ξ') (c₁ : κ) (h : genPt ξ ⤳ f p'.1), InChart ξ x c₁ ⟨f p'.1, h⟩ ↔ InChart ξ' (fun k => algebraMap Ω (GenField Ω r) (x k)) c₁ p') → Smooth f := by
  intro X Ω _ ξ E _ _ κ _ x S _ r V L m n φ c X' ξ' f hT hall hVB hTw hc hT' hall' hdom hch
  classical
  have hi : Function.Injective (algebraMap Ω (GenField Ω r)) := (algebraMap Ω (GenField Ω r)).injective
  refine GlobalTheory.T.dominating_pieces_smooth X X' Ω (GenField Ω r) ξ ξ' f (algebraMap Ω (GenField Ω r)) hT.gen hT'.gen hdom (fun p' => ?_)
  let P' : Cpt ξ' := ⟨p', hall' p'⟩
  obtain ⟨⟨c₀, J⟩, hcJ⟩ := hT'.cover P'
  have hy0 : flagCoord κ x φ c (c₀, J) ≠ 0 := hcJ.1
  have hx0 : x c₀ ≠ 0 := by
    intro h0
    apply hy0
    simp [flagCoord, h0]

  have hover : ∀ Q' : Cpt ξ', InChart ξ' (flagCoord κ x φ c) ((c₀, J) : FlagIx κ n r) Q' →
      InChart ξ x c₀ ⟨f Q'.1, hall _⟩ := by
    intro Q' hQ
    refine (hch Q' c₀ (hall _)).2 ⟨by simpa using hx0, fun k => ?_⟩
    have h := hQ.2 ((k, J) : FlagIx κ n r)
    have hpr : (∏ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det) ≠ 0 := by
      intro h0
      apply hy0
      simp [flagCoord, h0]
    have e : flagCoord κ x φ c ((k, J) : FlagIx κ n r) / flagCoord κ x φ c ((c₀, J) : FlagIx κ n r) =
        algebraMap Ω (GenField Ω r) (x k) / algebraMap Ω (GenField Ω r) (x c₀) := by
      simp only [flagCoord]
      have : algebraMap Ω (GenField Ω r) (x c₀) ≠ 0 := by simpa using hx0
      field_simp
    rwa [e] at h
  let P : Cpt ξ := ⟨f p', hall _⟩
  have h2 : InChart ξ x c₀ P := hover P' hcJ
  have hfr := fun s => GlobalTheory.T.twisted_frame_in_chart X Ω ξ E κ x (r s) (V s) (L s) (m s) (n s) (φ s) (c s) c₀ P hT hall (hVB s) (hTw s) (hc s) h2
  choose g hgR hgu T M N hT0 hM hN hNM hφ using hfr
  let g₀ : Ω := ∏ s, g s
  have hg₀R : g₀ ∈ chartSub x c₀ := Subring.prod_mem _ fun s _ => hgR s
  have hg₀0 : g₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => (hgu s).1
  have hreg : ∀ a ∈ chartSub x c₀, ∀ Q : Cpt ξ, InChart ξ x c₀ Q → a ∈ regAt ξ Q := fun a ha Q hQ =>
    (hT.ring c₀ hx0 a).1 ha Q hQ
  have hg₀inv : g₀⁻¹ ∈ regAt ξ P := by
    have : g₀⁻¹ = ∏ s, (g s)⁻¹ := by simp [g₀]
    rw [this]
    exact Subring.prod_mem _ fun s _ => (hgu s).2.2
  have hg₀u : unitAt ξ P g₀ := ⟨hg₀0, hreg _ hg₀R P h2, hg₀inv⟩
  let R : Subring Ω := locSub (chartSub x c₀) g₀
  have hle : ∀ s, locSub (chartSub x c₀) (g s) ≤ R := fun s =>
    locSub_le_of_mul (b := ∏ s' ∈ Finset.univ.erase s, g s')
      (Subring.prod_mem _ fun s' _ => hgR s') (Finset.mul_prod_erase Finset.univ g (Finset.mem_univ s)) hg₀0
  have hRP : ∀ a ∈ R, a ∈ regAt ξ P := by
    have : R ≤ regAt ξ P := (Subring.closure_le).2 (Set.union_subset (fun y hy => hreg y hy P h2)
      (by rintro _ rfl; exact hg₀inv))
    exact this
  obtain ⟨hPh, hdom1, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' (GenField Ω r) ξ' f _ hdom P'
  have hRO : ∀ a ∈ R, algebraMap Ω (GenField Ω r) a ∈ regAt ξ' P' := fun a ha => hdom1 a (hRP a ha)
  haveI : IsLocalRing (regAt ξ' P') := (regAt_isLocalRing_isFractionRing_stalk X' _ ξ' hT'.gen P').1
  have hscale : ∀ (k : κ) (J' : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), _ :=
    fun k J' => flagCoord_eq (m := m) x hφ k J'
  have hax : algebraMap Ω (GenField Ω r) (x c₀) ≠ 0 := by simpa using hx0
  have hprod0 := hscale c₀ J
  have hβ0 : ∀ q, stepMinor (flagB M T q.1) q.2 (J q) ≠ 0 := by
    intro q h0
    apply hy0
    rw [hprod0, Finset.prod_eq_zero (Finset.mem_univ q) (by rw [h0, mul_zero]), mul_zero]
  have hβJ : ∀ (q : Σ s, Fin (r s)) (J' : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)),
      stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) ∈ regAt ξ' P' := by
    intro q J'
    have h := hcJ.2 ((c₀, Function.update J q J') : FlagIx κ n r)
    rw [hscale c₀ (Function.update J q J'), hprod0, mul_div_mul_left _ _ hax,
      prod_update_div (β := fun q => Fin ((q.2 : ℕ) + 1) → Fin (n q.1))
        (fun q b => (algebraMap Ω (GenField Ω r) (x c₀) ^ m q.1) ^ ((q.2 : ℕ) + 1) * stepMinor (flagB M T q.1) q.2 b) J
        (fun q => mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hax)) (hβ0 q)) q J',
      mul_div_mul_left _ _ (pow_ne_zero _ (pow_ne_zero _ hax))] at h
    exact h
  obtain ⟨t, htR, ht0, htO, htiO, hmap, hsm⟩ := GlobalTheory.T.frame_matrices_regular_generic Ω S r n R (regAt ξ' P') T M N J hRO hT0
    (fun s j l => hle s (hM s j l)) (fun s l j => hle s (hN s l j)) hNM hβ0 hβJ
  obtain ⟨hgA, hAeq⟩ := GlobalTheory.T.chart_frame_matrix_regular Ω E κ x S r n m φ c M T c₀ J g₀ hx0 hg₀R hg₀0 hφ hβ0
  obtain ⟨U₀, hU₀, hU₀m⟩ := isPiece_chart hT hx0
  obtain ⟨U₁, hU₁, hU₁m⟩ := GlobalTheory.T.piece_localization_at_element X Ω ξ U₀ _ g₀ hT.gen hU₀ hg₀R hg₀0
  obtain ⟨W₀, hW₀, hW₀m⟩ := isPiece_chart (coordTie_int_inst _ hT') hy0
  have hig0 : algebraMap Ω (GenField Ω r) g₀ ≠ 0 := by simpa using hg₀0
  obtain ⟨W₁, hW₁, hW₁m⟩ := GlobalTheory.T.piece_localization_at_element X' _ ξ' W₀ _ _ hT'.gen hW₀ hgA hig0
  rw [hAeq] at hW₁
  obtain ⟨W₂, hW₂, hW₂m⟩ := GlobalTheory.T.piece_localization_at_element X' _ ξ' W₁ _ t hT'.gen hW₁ htR ht0
  refine ⟨U₁, W₂, R, _, hmap, hU₁, hW₂, ?_, ?_, hsm⟩
  · intro q' hq'
    let Q' : Cpt ξ' := ⟨q', hall' q'⟩
    have e1 := ((hW₂m Q').1 hq').1
    obtain ⟨e2, e3⟩ := (hW₁m Q').1 e1
    have e4 := (hW₀m Q').1 e2
    have e5 := hover Q' e4
    obtain ⟨h', -, hun⟩ := RegAtDom.regAt_dominates X Ω ξ X' (GenField Ω r) ξ' f _ hdom Q'
    exact (hU₁m ⟨f q', hall _⟩).2 ⟨(hU₀m _).2 e5, hun hT'.gen g₀ (hreg _ hg₀R _ e5) e3⟩
  · refine (hW₂m P').2 ⟨(hW₁m P').2 ⟨(hW₀m P').2 hcJ, hig0, hRO _ (le_locSub _ _ hg₀R), ?_⟩, ht0, htO, htiO⟩
    rw [← map_inv₀]
    exact hRO _ (inv_mem_locSub _ _)

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
