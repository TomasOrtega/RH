import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffMonicPolySum
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.LocSepTie

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Chain the equalities or inequalities of the calculation.
-/
theorem lpChar_zero_unr (w : PlE H) (χ : A.LP w) (hd : A.lpDim χ = 1) (hu : A.unr χ) :
    A.lpChar (A.lpZero w) χ = A.lpZero w := by
  have hu0 := A.lpZero_unr w
  have hc := A.unr_char _ _ hd hu0 hu
  have hcard := A.frobEig_card _ hc
  rw [A.lpDim_char _ _ hd, A.lpDim_zero] at hcard
  calc A.lpChar (A.lpZero w) χ = A.lpUnr w (A.frobEig (A.lpChar (A.lpZero w) χ)) := A.unr_eq_lpUnr _ hc
    _ = A.lpUnr w (A.frobEig (A.lpZero w)) := by rw [Multiset.card_eq_zero.mp hcard, A.frobEig_zero]
    _ = A.lpZero w := (A.unr_eq_lpUnr _ hu0).symm

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Simplify by unfolding definitions.

Replace the chosen expression with an arbitrary variable. Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.
-/
theorem spehLoc_twist_of_laws (hC : GlobalTheory.RowTie.CharLaws N A) (p : Part A.CG) (χ : A.CG 1) (w : PlE H)
    (hz : A.lpChar (A.lpZero w) (A.locG χ w) = A.lpZero w) :
    spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w = A.lpChar (spehLoc N A p w) (A.locG χ w) := by
  have hχ := A.locG_dim χ w
  have hsum : ∀ a b : A.LP w, A.lpChar (A.lpSum a b) (A.locG χ w) =
      A.lpSum (A.lpChar a (A.locG χ w)) (A.lpChar b (A.locG χ w)) := fun a b => (hC w a b _ _ 0 hχ hχ).1
  have htw : ∀ (a : A.LP w) (s : ℝ), A.lpChar (A.lpTw a s) (A.locG χ w) = A.lpTw (A.lpChar a (A.locG χ w)) s :=
    fun a s => (hC w a a _ _ s hχ hχ).2.1
  unfold spehLoc
  dsimp only
  generalize (List.range p.d >>= fun a : ℕ => (pure (a : ℝ) : List ℝ)) = l
  induction l with
  | nil => exact hz.symm
  | cons k l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih, hsum, htw, A.locG_tw]

/- English proof (translation)
Establish an intermediate fact. Proceed by induction. Treat this case separately. Treat this case separately. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities.
-/
theorem isoLoc_twist_of_laws (hC : GlobalTheory.RowTie.CharLaws N A) (S : List (Part A.CG)) (χ : A.CG 1) (w : PlE H)
    (hz : A.lpChar (A.lpZero w) (A.locG χ w) = A.lpZero w) :
    isoLoc N A (twistIso N A S χ) w = A.lpChar (isoLoc N A S w) (A.locG χ w) := by
  have hχ := A.locG_dim χ w
  induction S with
  | nil => exact hz.symm
  | cons p S ih =>
    change A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w) =
      A.lpChar (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (A.locG χ w)
    rw [ih, spehLoc_twist_of_laws N A hC p χ w hz, (hC w _ _ _ _ 0 hχ hχ).1]

/- English proof (translation)
Proceed by induction. Treat this case separately. Express the relevant assertion in an equivalent form by its definition. Treat this case separately. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isoLoc_append_one (S : List (Part A.CG)) (q : Part A.CG) (w : PlE H) :
    isoLoc N A (S ++ [q]) w = A.lpSum (isoLoc N A S w) (spehLoc N A q w) := by
  induction S with
  | nil =>
    change A.lpSum (spehLoc N A q w) (A.lpZero w) = A.lpSum (A.lpZero w) (spehLoc N A q w)
    exact A.lpSum_comm _ _
  | cons p S ih =>
    change A.lpSum (spehLoc N A p w) (isoLoc N A (S ++ [q]) w) =
      A.lpSum (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (spehLoc N A q w)
    rw [ih, A.lpSum_assoc]

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem heckePol_coeff (i : N.Loc) (x : N.X i) (w : PlE H) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ R.nV) :
    (heckePol N i x w).coeff (R.nV - k) =
      (-1 : N.O i) ^ k * ((normV w : ℕ) : N.O i) ^ (k * (k - 1) / 2) * ((N.hT i w k : N.X i → N.O i) x) := by
  unfold heckePol
  exact GlobalTheory.PtLocalEig.coeff_monic_poly_sum R.nV k hk1 hk2
    (fun k' => (-1 : N.O i) ^ k' * ((normV w : ℕ) : N.O i) ^ (k' * (k' - 1) / 2) * ((N.hT i w k' : N.X i → N.O i) x))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem main : ∀ (D : D7) (M : Formalism.L2.MtFam D), Formalism.L2.HeckeTied D M → GlobalTheory.RowTie.CharLaws D.nd D.naut →
    (∀ (i i' : D.nd.Loc) (σ : D.what₂.FT) (v : PlE D.host), IsSplitPl D.host v →
      D.naut.locW i σ v = D.naut.locW i' σ v) →
    (∀ i i' : D.nd.Loc, D.nd.j i = D.nd.j i' → D.nd.w i = D.nd.w i' → D.naut.muC i = D.naut.muC i') →
    KillingConditions.LocalisationUniqueness D := by
  intro D M HT hC hW hmu
  unfold KillingConditions.LocalisationUniqueness
  intro i i' _ hj hw σ _ hA hA'
  by_contra hne
  obtain ⟨φ, hφ⟩ := HT.sameO i i' hj hw
  obtain ⟨Sig, hSig, x, hx⟩ := hA
  obtain ⟨Sig', hSig', x', hx'⟩ := hA'
  obtain ⟨v, k, hv, hv', hk1, hk2, hunit⟩ := HT.sep i i' φ hφ hj hw hne x x'
  obtain ⟨p, hp1, hp2⟩ := hx v hv
  obtain ⟨p', hp1', hp2'⟩ := hx' v hv'
  have hinj' : Function.Injective (iotaO D.nd D.naut i') := by
    unfold iotaO
    simp only [RingHom.coe_comp]
    exact (D.naut.iotaQC i').injective.comp ((D.naut.iotaQ i').injective.comp
      (IsFractionRing.injective (D.nd.O i') (FractionRing (D.nd.O i'))))
  have hmuP : muPart D.nd D.naut i = muPart D.nd D.naut i' := by
    unfold muPart; rw [hmu i i' hj hw]
  have hz := lpChar_zero_unr D.nd D.naut v (D.naut.locG D.naut.etaTinv v) (D.naut.locG_dim _ v)
    (D.naut.etaTinv_def v).1
  have hpar : isoLoc D.nd D.naut (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) v =
      isoLoc D.nd D.naut (twistIso D.nd D.naut (Sig' ++ [muPart D.nd D.naut i']) D.naut.etaTinv) v := by
    rw [isoLoc_twist_of_laws D.nd D.naut hC _ _ v hz, isoLoc_twist_of_laws D.nd D.naut hC _ _ v hz,
      isoLoc_append_one, isoLoc_append_one, hSig.2.2 v hv.1, hSig'.2.2 v hv'.1, hW i i' σ v hv.1, hmuP]
  have hpp : p.map (φ : D.nd.O i →+* D.nd.O i') = p' := by
    apply Polynomial.map_injective (iotaO D.nd D.naut i') hinj'
    rw [Polynomial.map_map, hp1', ← hpar, ← hp1]
    congr 1
    exact RingHom.ext fun z => (hφ z).symm
  set n := D.R.nV - k
  have e1 : IsLocalRing.residue (D.nd.O i) (p.coeff n) =
      IsLocalRing.residue (D.nd.O i) ((heckePol D.nd i x v).coeff n) := by
    have := congrArg (fun P => Polynomial.coeff P n) hp2
    simpa only [Polynomial.coeff_map] using this
  have e2 : IsLocalRing.residue (D.nd.O i') (p'.coeff n) =
      IsLocalRing.residue (D.nd.O i') ((heckePol D.nd i' x' v).coeff n) := by
    have := congrArg (fun P => Polynomial.coeff P n) hp2'
    simpa only [Polynomial.coeff_map] using this
  have e3 := GlobalTheory.PtLocalEig.residue_map_equiv φ e1
  have hcp : φ (p.coeff n) = p'.coeff n := by
    rw [← hpp, Polynomial.coeff_map]; rfl
  have hφc : φ ((-1 : D.nd.O i) ^ k * ((normV v : ℕ) : D.nd.O i) ^ (k * (k - 1) / 2) *
      ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x)) = (-1 : D.nd.O i') ^ k * ((normV v : ℕ) : D.nd.O i') ^ (k * (k - 1) / 2) *
      φ ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) := by
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
  rw [hcp, e2, heckePol_coeff D.nd i x v k hk1 hk2, heckePol_coeff D.nd i' x' v k hk1 hk2, hφc] at e3
  have hq := GlobalTheory.PtLocalEig.normV_unit D i' v hv'.2.1
  have hc : IsUnit ((-1 : D.nd.O i') ^ k * ((normV v : ℕ) : D.nd.O i') ^ (k * (k - 1) / 2)) :=
    ((isUnit_one.neg).pow k).mul (hq.pow _)
  have hdiff : IsLocalRing.residue (D.nd.O i')
      ((-1 : D.nd.O i') ^ k * ((normV v : ℕ) : D.nd.O i') ^ (k * (k - 1) / 2) *
        (φ ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) - (D.nd.hT i' v k : D.nd.X i' → D.nd.O i') x')) = 0 := by
    rw [mul_sub, map_sub, e3, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hdiff
  exact hdiff (hc.mul hunit)

end GlobalTheory.LocSepTie
