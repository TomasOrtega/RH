import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PNoLogLie
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PNoLogOde
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PNoLogQ
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PSepFacB
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermTranslateFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAutomorphicCriterionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDeterminantPolynomialCoefficientsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliOperatorsCommuteStatement

noncomputable section

open NumberField Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs MeasureTheory

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms

open SepFac

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

section Sp

variable (r s : ℕ) (m : (E →+* ℂ) → Multiset ℂ)

def Vsp : Submodule ℂ (Sm E (r + s)) where
  carrier := {Φ | (∀ (x : BlockIx (r + s) r → Ad E) g, Φ.1 (unip x * g) = Φ.1 g) ∧
    ∀ τ u, cap τ u Φ = ((m τ).map (u + ·)).prod • Φ}
  add_mem' := fun {Φ Ψ} hΦ hΨ => ⟨fun x g => by
      simp only [Submodule.coe_add, Pi.add_apply, hΦ.1 x g, hΨ.1 x g], fun τ u => by
      rw [map_add, hΦ.2, hΨ.2, smul_add]⟩
  zero_mem' := ⟨fun _ _ => rfl, fun τ u => by simp⟩
  smul_mem' := fun c Φ hΦ => ⟨fun x g => by
      simp only [Submodule.coe_smul, Pi.smul_apply, hΦ.1 x g], fun τ u => by
      rw [map_smul, hΦ.2, smul_comm]⟩

def Isp : Submodule ℂ (Sm E (r + s)) where
  carrier := {Φ | Φ ∈ Vsp r s m ∧ ∀ p : GA E r × GA E s, Φ.1 (lev (Ad E) r s p) = 0}
  add_mem' := fun {Φ Ψ} hΦ hΨ => ⟨(Vsp r s m).add_mem hΦ.1 hΨ.1, fun p => by
      simp only [Submodule.coe_add, Pi.add_apply, hΦ.2 p, hΨ.2 p, add_zero]⟩
  zero_mem' := ⟨(Vsp r s m).zero_mem, fun _ => rfl⟩
  smul_mem' := fun c Φ hΦ => ⟨(Vsp r s m).smul_mem c hΦ.1, fun p => by
      simp only [Submodule.coe_smul, Pi.smul_apply, hΦ.2 p, smul_zero]⟩

/- English proof (translation)
Use `⟨fun x g => ?_, fun τ u => ?_⟩` and prove the remaining obligations. Establish `e : JFinTr.ltr (unip x) Φ = Φ` using `Subtype.ext (funext fun g => hΦ.1 x g)`. Establish `h` using `congrArg (fun ψ : Sm E (r + s) => ψ.1 g) (LinearMap.congr_fun (Sl_comm_ltr (unip x) hT).eq Φ)`. Simplify using `only [Module.End.mul_apply, e] at h`. Conclude with `h`.

Rewrite using `[← Module.End.mul_apply, (Sl_comm_cap τ u hT).eq, Module.End.mul_apply, hΦ.2, map_smul]`.
-/
theorem Sl_mapsTo {T : Module.End ℂ (Sm E (r + s))} (hT : T ∈ Sl (r + s)) {Φ : Sm E (r + s)}
    (hΦ : Φ ∈ Vsp r s m) : T Φ ∈ Vsp r s m := by
  refine ⟨fun x g => ?_, fun τ u => ?_⟩
  · have e : JFinTr.ltr (unip x) Φ = Φ := Subtype.ext (funext fun g => hΦ.1 x g)
    have h := congrArg (fun ψ : Sm E (r + s) => ψ.1 g) (LinearMap.congr_fun (Sl_comm_ltr (unip x) hT).eq Φ)
    simp only [Module.End.mul_apply, e] at h
    exact h
  · rw [← Module.End.mul_apply, (Sl_comm_cap τ u hT).eq, Module.End.mul_apply, hΦ.2, map_smul]

/- English proof (translation)
The claim follows from `qdet_mem _ _ (fun _ _ => Eop_mem_Sl τ _ _) _`.
-/
theorem capR_mem_Sl (τ : E →+* ℂ) (u : ℂ) : capR r s τ u ∈ Sl (E := E) (r + s) :=
  qdet_mem _ _ (fun _ _ => Eop_mem_Sl τ _ _) _

/- English proof (translation)
The claim follows from `qdet_mem _ _ (fun _ _ => Eop_mem_Sl τ _ _) _`.
-/
theorem capS_mem_Sl (τ : E →+* ℂ) (u : ℂ) : capS r s τ u ∈ Sl (E := E) (r + s) :=
  qdet_mem _ _ (fun _ _ => Eop_mem_Sl τ _ _) _

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ hv => Sl_mapsTo r s m (capR_mem_Sl r s τ u) hv, fun _ hv => ⟨Sl_mapsTo r s m (capR_mem_Sl r s τ u) hv.1, ((CapStable.capStable E r s τ u _).1 hv.2).1⟩⟩`.
-/
theorem capR_mem_Pa (τ : E →+* ℂ) (u : ℂ) : capR r s τ u ∈ Pa (Vsp r s m) (Isp r s m) :=
  ⟨fun _ hv => Sl_mapsTo r s m (capR_mem_Sl r s τ u) hv, fun _ hv =>
    ⟨Sl_mapsTo r s m (capR_mem_Sl r s τ u) hv.1, ((CapStable.capStable E r s τ u _).1 hv.2).1⟩⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ hv => Sl_mapsTo r s m (capS_mem_Sl r s τ u) hv, fun _ hv => ⟨Sl_mapsTo r s m (capS_mem_Sl r s τ u) hv.1, ((CapStable.capStable E r s τ u _).1 hv.2).2⟩⟩`.
-/
theorem capS_mem_Pa (τ : E →+* ℂ) (u : ℂ) : capS r s τ u ∈ Pa (Vsp r s m) (Isp r s m) :=
  ⟨fun _ hv => Sl_mapsTo r s m (capS_mem_Sl r s τ u) hv, fun _ hv =>
    ⟨Sl_mapsTo r s m (capS_mem_Sl r s τ u) hv.1, ((CapStable.capStable E r s τ u _).1 hv.2).2⟩⟩

end Sp

section Key

variable (r s : ℕ) (m : (E →+* ℂ) → Multiset ℂ)

/- English proof (translation)
Establish `h1 : Submodule.span ℂ (Set.range S) ≤ Subalgebra.toSubmodule (Subalgebra.centralizer ℂ (Set.range R))`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨v, rfl⟩`. Simplify using `only [Subalgebra.coe_toSubmodule, Subalgebra.coe_centralizer, Set.mem_centralizer_iff, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]`. Conclude with `fun u => (h u v).eq`.

Establish `hy' : ∀ u, Commute (R u) y` using `fun u => (Subalgebra.mem_centralizer_iff ℂ).1 (h1 hy) _ ⟨u, rfl⟩`. Establish `h2 : Submodule.span ℂ (Set.range R) ≤ Subalgebra.toSubmodule (Subalgebra.centralizer ℂ {y})`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨u, rfl⟩`. Simplify using `only [Subalgebra.coe_toSubmodule, Subalgebra.coe_centralizer, Set.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]`.

Conclude with `(hy' u).eq.symm`. Conclude with `((Subalgebra.mem_centralizer_iff ℂ).1 (h2 hx) y rfl).symm`.
-/
theorem commute_span {A : Type} [Ring A] [Algebra ℂ A] {R S : ℂ → A} (h : ∀ u v, Commute (R u) (S v)) {x y : A}
    (hx : x ∈ Submodule.span ℂ (Set.range R)) (hy : y ∈ Submodule.span ℂ (Set.range S)) : Commute x y := by
  have h1 : Submodule.span ℂ (Set.range S) ≤ Subalgebra.toSubmodule (Subalgebra.centralizer ℂ (Set.range R)) := by
    rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    simp only [Subalgebra.coe_toSubmodule, Subalgebra.coe_centralizer, Set.mem_centralizer_iff, Set.mem_range,
      forall_exists_index, forall_apply_eq_imp_iff]
    exact fun u => (h u v).eq
  have hy' : ∀ u, Commute (R u) y := fun u => (Subalgebra.mem_centralizer_iff ℂ).1 (h1 hy) _ ⟨u, rfl⟩
  have h2 : Submodule.span ℂ (Set.range R) ≤ Subalgebra.toSubmodule (Subalgebra.centralizer ℂ {y}) := by
    rw [Submodule.span_le]
    rintro _ ⟨u, rfl⟩
    simp only [Subalgebra.coe_toSubmodule, Subalgebra.coe_centralizer, Set.mem_centralizer_iff,
      Set.mem_singleton_iff, forall_eq]
    exact (hy' u).eq.symm
  exact ((Subalgebra.mem_centralizer_iff ℂ).1 (h2 hx) y rfl).symm

end Key

section Key2

variable (r s : ℕ) (m : (E →+* ℂ) → Multiset ℂ)

def X1 (τ : E →+* ℂ) : Fin r → Fin r → Module.End ℂ (Sm E (r + s)) :=
  fun i j => Eop τ (Fin.castAdd s i) (Fin.castAdd s j)

def X2 (τ : E →+* ℂ) : Fin s → Fin s → Module.End ℂ (Sm E (r + s)) :=
  fun i j => Eop τ (Fin.natAdd r i) (Fin.natAdd r j)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem capR_eq (τ : E →+* ℂ) (u : ℂ) : capR r s τ u = Formalism.REAL.qdet (X1 r s τ) (u + ((r : ℂ) - 1) / 2) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem capS_eq (τ : E →+* ℂ) (u : ℂ) : capS r s τ u = Formalism.REAL.qdet (X2 r s τ) (u + ((s : ℂ) - 1) / 2) := rfl

/- English proof (translation)
The claim follows from `Subtype.ext h`.
-/
theorem commute_val {x y : Pa (Vsp r s m) (Isp r s m)} (h : Commute x.1 y.1) : Commute x y := Subtype.ext h

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `set V := Vsp r s m`. Use `set I := Isp r s m`. Use `set π := piQ V I`. Use `set c₁ : ℂ := ((r : ℂ) - 1) / 2 - (s : ℂ) / 2 with hc₁`. Use `set c₂ : ℂ := (r : ℂ) / 2 + ((s : ℂ) - 1) / 2 with hc₂`.

Take `⟨a, ha1, haspan, haeq⟩` from `GlobalTheory.T.quantum_determinant_polynomial_coefficients _ r (X1 r s τ) c₁`. Take `⟨b, hb1, hbspan, hbeq⟩` from `GlobalTheory.T.quantum_determinant_polynomial_coefficients _ s (X2 r s τ) c₂`. Establish `hqa : ∀ u, Formalism.REAL.qdet (X1 r s τ) (u + c₁) = capR r s τ (u - (s : ℂ) / 2)` using `fun u => by`. Rewrite using `[capR_eq]`. Use `congr 1`.

Rewrite using `[hc₁]`. Expand and normalize the polynomial expressions, which then agree. Establish `hqb : ∀ u, Formalism.REAL.qdet (X2 r s τ) (u + c₂) = capS r s τ (u + (r : ℂ) / 2)` using `fun u => by`. Rewrite using `[capS_eq]`. Use `congr 1`.

Rewrite using `[hc₂]`. Expand and normalize the polynomial expressions, which then agree. Establish `hPa : Submodule.span ℂ (Set.range fun u => Formalism.REAL.qdet (X1 r s τ) (u + c₁)) ≤ Subalgebra.toSubmodule (Pa V I)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨u, rfl⟩`.

Use `show Formalism.REAL.qdet (X1 r s τ) (u + c₁) ∈ Pa V I`. Rewrite using `[hqa]`. Conclude with `capR_mem_Pa r s m τ _`. Establish `hPb : Submodule.span ℂ (Set.range fun u => Formalism.REAL.qdet (X2 r s τ) (u + c₂)) ≤ Subalgebra.toSubmodule (Pa V I)`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨u, rfl⟩`. Use `show Formalism.REAL.qdet (X2 r s τ) (u + c₂) ∈ Pa V I`. Rewrite using `[hqb]`. Conclude with `capS_mem_Pa r s m τ _`. Set `aP : ℕ → Pa V I` to `fun k => ⟨a k, hPa (haspan k)⟩`.

Set `bP : ℕ → Pa V I` to `fun k => ⟨b k, hPb (hbspan k)⟩`. Establish `hRP : ∀ u, (⟨capR r s τ u, capR_mem_Pa r s m τ u⟩ : Pa V I) = ∑ k ∈ Finset.range (r + 1), (u + (s : ℂ) / 2) ^ k • aP k` using `fun u => by`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `e` using `haeq (u + (s : ℂ) / 2)`. Rewrite `e` using `[hqa, add_sub_cancel_right]`.

Use `show capR r s τ u = _`. Rewrite using `[e]`. Simplify using `[aP]`. Establish `hSP : ∀ u, (⟨capS r s τ u, capS_mem_Pa r s m τ u⟩ : Pa V I) = ∑ k ∈ Finset.range (s + 1), (u - (r : ℂ) / 2) ^ k • bP k` using `fun u => by`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `e` using `hbeq (u - (r : ℂ) / 2)`. Rewrite `e` using `[hqb, sub_add_cancel]`. Use `show capS r s τ u = _`. Rewrite using `[e]`. Simplify using `[bP]`.

Establish `hcRR` using `fun u v => (GlobalTheory.T.capelli_operators_commute E r s τ u v).1`. Establish `hcRS` using `fun u v => (GlobalTheory.T.capelli_operators_commute E r s τ u v).2.1`. Establish `hcSS` using `fun u v => (GlobalTheory.T.capelli_operators_commute E r s τ u v).2.2`. Establish `hcab : ∀ i j, Commute (aP i) (aP j) ∧ Commute (aP i) (bP j) ∧ Commute (bP i) (bP j)` using `fun i j => by`. Use `⟨commute_val r s m ?_, commute_val r s m ?_, commute_val r s m ?_⟩` and prove the remaining obligations.

Conclude with `commute_span (fun u v => by rw [hqa, hqa]; exact hcRR _ _) (haspan i) (haspan j)`. Conclude with `commute_span (fun u v => by rw [hqa, hqb]; exact hcRS _ _) (haspan i) (hbspan j)`. Conclude with `commute_span (fun u v => by rw [hqb, hqb]; exact hcSS _ _) (hbspan i) (hbspan j)`. Establish `hrel : ∀ u : ℂ, (∑ k ∈ Finset.range (s + 1), (u + 0) ^ k • π (bP k)) * (∑ k ∈ Finset.range (r + 1), (u + 0) ^ k • π (aP k)) = algebraMap ℂ _ ((m τ).map (u + ·)).prod`. Introduce `u`.

Establish `e1 : (∑ k ∈ Finset.range (s + 1), (u + 0) ^ k • π (bP k)) = π ⟨capS r s τ (u + (r : ℂ) / 2), capS_mem_Pa r s m τ _⟩`. Rewrite using `[hSP, map_sum]`. Simplify using `[map_smul]`. Establish `e2 : (∑ k ∈ Finset.range (r + 1), (u + 0) ^ k • π (aP k)) = π ⟨capR r s τ (u - (s : ℂ) / 2), capR_mem_Pa r s m τ _⟩`. Rewrite using `[hRP, map_sum]`.

Simplify using `[map_smul]`. Establish `e3 : π (⟨capS r s τ (u + (r : ℂ) / 2), capS_mem_Pa r s m τ _⟩ * ⟨capR r s τ (u - (s : ℂ) / 2), capR_mem_Pa r s m τ _⟩) = algebraMap ℂ _ ((m τ).map (u + ·)).prod`. Use `piQ_eq_algebraMap V I _ fun v hv => ⟨V.sub_mem (((Pa V I).mul_mem (capS_mem_Pa r s m τ _) (capR_mem_Pa r s m τ _)).1 v hv) (V.smul_mem _ hv), fun p => ?_⟩` and prove the remaining obligations. Establish `h1` using `CapFactor.cap_levi E r s τ u v hv.1 p`. Rewrite `h1` using `[hv.2]`.

Express the relevant statement in the definitionally equal form `(capS r s τ (u + (r : ℂ) / 2) (capR r s τ (u - (s : ℂ) / 2) v)).1 (lev (Ad E) r s p) - (((m τ).map (u + ·)).prod • v).1 (lev (Ad E) r s p) = 0`. Rewrite using `[← h1, sub_self]`. Combine the equalities or inequalities in the displayed calculation. Establish `hb1' : π (bP s) = 1`. Rewrite using `[show bP s = 1 from Subtype.ext hb1, map_one]`.

Establish `ha1' : π (aP r) = 1`. Rewrite using `[show aP r = 1 from Subtype.ext ha1, map_one]`. Establish `hss : ∀ k ≤ r, IsSS (π (aP k))` using `fun k hk => (isSS_coeff_fun (m τ) (hm τ).1 s r (by rw [(hm τ).2, add_comm]) 0 0 (fun k => π (bP k)) (fun k => π (aP k)) hb1' ha1' (fun i j => ⟨((hcab i j).2.2).map π, ((hcab j i).2.1).symm.map π, ((hcab i j).1).map π⟩) hrel k).2 hk`. Establish `hR : ∀ u, IsSS (π ⟨capR r s τ u, capR_mem_Pa r s m τ u⟩)` using `fun u => by`. Rewrite using `[hRP, map_sum]`.

Use `IsSS.sum _ _ (fun k hk => ?_) (fun i _ j _ => ?_)` and prove the remaining obligations. Rewrite using `[map_smul]`. Conclude with `(hss k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))).smul _`. Rewrite using `[map_smul, map_smul]`. Conclude with `(((hcab i j).1).map π).smul_left _ |>.smul_right _`.

Establish `hT : Tr1 r s τ ∈ Algebra.adjoin ℂ (Set.range (capR r s τ))` using `GlobalTheory.CapTrace.trace_mem_of_qdet_mem (X1 r s τ) _ fun u => by`. Establish `e : Formalism.REAL.qdet (X1 r s τ) u = capR r s τ (u - ((r : ℂ) - 1) / 2)`. Rewrite using `[capR_eq]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `Algebra.subset_adjoin ⟨_, rfl⟩`. Set `RPf : ℂ → Pa V I` to `fun u => ⟨capR r s τ u, capR_mem_Pa r s m τ u⟩`. Establish `himg : Set.range (capR r s τ) = (Pa V I).val '' Set.range RPf`. Rewrite using `[← Set.range_comp]`.

Both sides reduce to the same expression. Rewrite `hT` using `[himg, Algebra.adjoin_image]`. Take `⟨x, hx, hxe⟩` from `Subalgebra.mem_map.1 hT`. Use `⟨x, hxe, ?_⟩` and prove the remaining obligations. Establish `hx' : π x ∈ (Algebra.adjoin ℂ (Set.range RPf)).map π` using `Subalgebra.mem_map.2 ⟨x, hx, rfl⟩`.

Rewrite `hx'` using `[AlgHom.map_adjoin]`. Use `IsSS.adjoin ?_ ?_ _ hx'` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨u, rfl⟩, rfl⟩`. Conclude with `hR u`. Introduce and unpack `_ ⟨_, ⟨u, rfl⟩, rfl⟩ _ ⟨_, ⟨v, rfl⟩, rfl⟩`.

Conclude with `(commute_val r s m (hcRR u v)).map π`.
-/
theorem trace_ss (hm : ∀ τ, (m τ).Nodup ∧ Multiset.card (m τ) = r + s) (τ : E →+* ℂ) :
    ∃ x : Pa (Vsp r s m) (Isp r s m), x.1 = Tr1 r s τ ∧ IsSS (piQ (Vsp r s m) (Isp r s m) x) := by
  classical
  set V := Vsp r s m
  set I := Isp r s m
  set π := piQ V I
  set c₁ : ℂ := ((r : ℂ) - 1) / 2 - (s : ℂ) / 2 with hc₁
  set c₂ : ℂ := (r : ℂ) / 2 + ((s : ℂ) - 1) / 2 with hc₂
  obtain ⟨a, ha1, haspan, haeq⟩ := GlobalTheory.T.quantum_determinant_polynomial_coefficients _ r (X1 r s τ) c₁
  obtain ⟨b, hb1, hbspan, hbeq⟩ := GlobalTheory.T.quantum_determinant_polynomial_coefficients _ s (X2 r s τ) c₂
  have hqa : ∀ u, Formalism.REAL.qdet (X1 r s τ) (u + c₁) = capR r s τ (u - (s : ℂ) / 2) := fun u => by
    rw [capR_eq]; congr 1; rw [hc₁]; ring
  have hqb : ∀ u, Formalism.REAL.qdet (X2 r s τ) (u + c₂) = capS r s τ (u + (r : ℂ) / 2) := fun u => by
    rw [capS_eq]; congr 1; rw [hc₂]; ring
  have hPa : Submodule.span ℂ (Set.range fun u => Formalism.REAL.qdet (X1 r s τ) (u + c₁)) ≤
      Subalgebra.toSubmodule (Pa V I) := by
    rw [Submodule.span_le]
    rintro _ ⟨u, rfl⟩
    show Formalism.REAL.qdet (X1 r s τ) (u + c₁) ∈ Pa V I
    rw [hqa]
    exact capR_mem_Pa r s m τ _
  have hPb : Submodule.span ℂ (Set.range fun u => Formalism.REAL.qdet (X2 r s τ) (u + c₂)) ≤
      Subalgebra.toSubmodule (Pa V I) := by
    rw [Submodule.span_le]
    rintro _ ⟨u, rfl⟩
    show Formalism.REAL.qdet (X2 r s τ) (u + c₂) ∈ Pa V I
    rw [hqb]
    exact capS_mem_Pa r s m τ _
  let aP : ℕ → Pa V I := fun k => ⟨a k, hPa (haspan k)⟩
  let bP : ℕ → Pa V I := fun k => ⟨b k, hPb (hbspan k)⟩
  have hRP : ∀ u, (⟨capR r s τ u, capR_mem_Pa r s m τ u⟩ : Pa V I) =
      ∑ k ∈ Finset.range (r + 1), (u + (s : ℂ) / 2) ^ k • aP k := fun u => by
    apply Subtype.ext
    have e := haeq (u + (s : ℂ) / 2)
    rw [hqa, add_sub_cancel_right] at e
    show capR r s τ u = _
    rw [e]
    simp [aP]
  have hSP : ∀ u, (⟨capS r s τ u, capS_mem_Pa r s m τ u⟩ : Pa V I) =
      ∑ k ∈ Finset.range (s + 1), (u - (r : ℂ) / 2) ^ k • bP k := fun u => by
    apply Subtype.ext
    have e := hbeq (u - (r : ℂ) / 2)
    rw [hqb, sub_add_cancel] at e
    show capS r s τ u = _
    rw [e]
    simp [bP]

  have hcRR := fun u v => (GlobalTheory.T.capelli_operators_commute E r s τ u v).1
  have hcRS := fun u v => (GlobalTheory.T.capelli_operators_commute E r s τ u v).2.1
  have hcSS := fun u v => (GlobalTheory.T.capelli_operators_commute E r s τ u v).2.2
  have hcab : ∀ i j, Commute (aP i) (aP j) ∧ Commute (aP i) (bP j) ∧ Commute (bP i) (bP j) := fun i j => by
    refine ⟨commute_val r s m ?_, commute_val r s m ?_, commute_val r s m ?_⟩
    · exact commute_span (fun u v => by rw [hqa, hqa]; exact hcRR _ _) (haspan i) (haspan j)
    · exact commute_span (fun u v => by rw [hqa, hqb]; exact hcRS _ _) (haspan i) (hbspan j)
    · exact commute_span (fun u v => by rw [hqb, hqb]; exact hcSS _ _) (hbspan i) (hbspan j)

  have hrel : ∀ u : ℂ, (∑ k ∈ Finset.range (s + 1), (u + 0) ^ k • π (bP k)) *
      (∑ k ∈ Finset.range (r + 1), (u + 0) ^ k • π (aP k)) = algebraMap ℂ _ ((m τ).map (u + ·)).prod := by
    intro u
    have e1 : (∑ k ∈ Finset.range (s + 1), (u + 0) ^ k • π (bP k)) =
        π ⟨capS r s τ (u + (r : ℂ) / 2), capS_mem_Pa r s m τ _⟩ := by
      rw [hSP, map_sum]; simp [map_smul]
    have e2 : (∑ k ∈ Finset.range (r + 1), (u + 0) ^ k • π (aP k)) =
        π ⟨capR r s τ (u - (s : ℂ) / 2), capR_mem_Pa r s m τ _⟩ := by
      rw [hRP, map_sum]; simp [map_smul]
    have e3 : π (⟨capS r s τ (u + (r : ℂ) / 2), capS_mem_Pa r s m τ _⟩ *
        ⟨capR r s τ (u - (s : ℂ) / 2), capR_mem_Pa r s m τ _⟩) = algebraMap ℂ _ ((m τ).map (u + ·)).prod := by
      refine piQ_eq_algebraMap V I _ fun v hv => ⟨V.sub_mem (((Pa V I).mul_mem (capS_mem_Pa r s m τ _)
        (capR_mem_Pa r s m τ _)).1 v hv) (V.smul_mem _ hv), fun p => ?_⟩
      have h1 := CapFactor.cap_levi E r s τ u v hv.1 p
      rw [hv.2] at h1
      change (capS r s τ (u + (r : ℂ) / 2) (capR r s τ (u - (s : ℂ) / 2) v)).1 (lev (Ad E) r s p) -
        (((m τ).map (u + ·)).prod • v).1 (lev (Ad E) r s p) = 0
      rw [← h1, sub_self]
    calc _ = π ⟨capS r s τ (u + (r : ℂ) / 2), capS_mem_Pa r s m τ _⟩ *
          π ⟨capR r s τ (u - (s : ℂ) / 2), capR_mem_Pa r s m τ _⟩ := by rw [e1, e2]
      _ = _ := by rw [← map_mul]; exact e3
  have hb1' : π (bP s) = 1 := by
    rw [show bP s = 1 from Subtype.ext hb1, map_one]
  have ha1' : π (aP r) = 1 := by
    rw [show aP r = 1 from Subtype.ext ha1, map_one]
  have hss : ∀ k ≤ r, IsSS (π (aP k)) := fun k hk =>
    (isSS_coeff_fun (m τ) (hm τ).1 s r (by rw [(hm τ).2, add_comm]) 0 0 (fun k => π (bP k)) (fun k => π (aP k))
      hb1' ha1' (fun i j => ⟨((hcab i j).2.2).map π, ((hcab j i).2.1).symm.map π, ((hcab i j).1).map π⟩)
      hrel k).2 hk

  have hR : ∀ u, IsSS (π ⟨capR r s τ u, capR_mem_Pa r s m τ u⟩) := fun u => by
    rw [hRP, map_sum]
    refine IsSS.sum _ _ (fun k hk => ?_) (fun i _ j _ => ?_)
    · rw [map_smul]
      exact (hss k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))).smul _
    · rw [map_smul, map_smul]
      exact (((hcab i j).1).map π).smul_left _ |>.smul_right _

  have hT : Tr1 r s τ ∈ Algebra.adjoin ℂ (Set.range (capR r s τ)) :=
    GlobalTheory.CapTrace.trace_mem_of_qdet_mem (X1 r s τ) _ fun u => by
      have e : Formalism.REAL.qdet (X1 r s τ) u = capR r s τ (u - ((r : ℂ) - 1) / 2) := by
        rw [capR_eq]; congr 1; ring
      rw [e]
      exact Algebra.subset_adjoin ⟨_, rfl⟩
  let RPf : ℂ → Pa V I := fun u => ⟨capR r s τ u, capR_mem_Pa r s m τ u⟩
  have himg : Set.range (capR r s τ) = (Pa V I).val '' Set.range RPf := by
    rw [← Set.range_comp]; rfl
  rw [himg, Algebra.adjoin_image] at hT
  obtain ⟨x, hx, hxe⟩ := Subalgebra.mem_map.1 hT
  refine ⟨x, hxe, ?_⟩
  have hx' : π x ∈ (Algebra.adjoin ℂ (Set.range RPf)).map π := Subalgebra.mem_map.2 ⟨x, hx, rfl⟩
  rw [AlgHom.map_adjoin] at hx'
  refine IsSS.adjoin ?_ ?_ _ hx'
  · rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    exact hR u
  · rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩ _ ⟨_, ⟨v, rfl⟩, rfl⟩
    exact (commute_val r s m (hcRR u v)).map π

/- English proof (translation)
Use `set V := Vsp r s m`. Use `set I := Isp r s m`. Use `set π := piQ V I`. Use `choose TP hTP1 hTP2 using trace_ss r s m hm`. Set `LZ : Pa V I` to `∑ w : InfinitePlace E, (TP w.embedding + TP (ComplexEmbedding.conjugate w.embedding))`.

Establish `hLZ : LZ.1 = lie E (r + s) (Zr (r + s) r)`. Rewrite using `[lie_Zr]`. Simplify using `only [LZ, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_add, hTP1]`. Establish `hc : ∀ τ τ', Commute (π (TP τ)) (π (TP τ'))` using `fun τ τ' => (commute_val r s m (by rw [hTP1, hTP1]; exact Tr1_comm r s τ τ')).map π`. Establish `hss : IsSS (π LZ)`.

Simplify using `only [LZ, map_sum, map_add]`. Use `IsSS.sum _ _ (fun w _ => (hTP2 _).add (hTP2 _) (hc _ _)) (fun w _ w' _ => ?_)` and prove the remaining obligations. Conclude with `((hc _ _).add_left (hc _ _)).add_right ((hc _ _).add_left (hc _ _))`. Take `⟨S, hS⟩` from `hss`. Use `⟨S, fun Φ hΦ p => ?_⟩` and prove the remaining obligations.

Establish `h0 : π (aeval LZ (∏ v ∈ S, (X - C v))) = 0`. Rewrite using `[← Polynomial.aeval_algHom_apply]`. Conclude with `hS`. Establish `h2` using `piQ_eq_zero V I h0 Φ hΦ`. Establish `e : (aeval LZ (∏ v ∈ S, (X - C v))).1 = aeval (lie E (r + s) (Zr (r + s) r)) (∏ v ∈ S, (X - C v))`.

Rewrite using `[← hLZ]`. Conclude with `(Polynomial.aeval_algHom_apply (Pa V I).val LZ _).symm`. Rewrite using `[← e]`. Conclude with `h2.2 p`.
-/
theorem key (hm : ∀ τ, (m τ).Nodup ∧ Multiset.card (m τ) = r + s) :
    ∃ S : Finset ℂ, ∀ Φ ∈ Vsp r s m, ∀ p : GA E r × GA E s,
      (aeval (lie E (r + s) (Zr (r + s) r)) (∏ v ∈ S, (X - C v)) Φ).1 (lev (Ad E) r s p) = 0 := by
  classical
  set V := Vsp r s m
  set I := Isp r s m
  set π := piQ V I
  choose TP hTP1 hTP2 using trace_ss r s m hm
  let LZ : Pa V I := ∑ w : InfinitePlace E, (TP w.embedding + TP (ComplexEmbedding.conjugate w.embedding))
  have hLZ : LZ.1 = lie E (r + s) (Zr (r + s) r) := by
    rw [lie_Zr]
    simp only [LZ, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_add, hTP1]
  have hc : ∀ τ τ', Commute (π (TP τ)) (π (TP τ')) := fun τ τ' =>
    (commute_val r s m (by rw [hTP1, hTP1]; exact Tr1_comm r s τ τ')).map π
  have hss : IsSS (π LZ) := by
    simp only [LZ, map_sum, map_add]
    refine IsSS.sum _ _ (fun w _ => (hTP2 _).add (hTP2 _) (hc _ _)) (fun w _ w' _ => ?_)
    exact ((hc _ _).add_left (hc _ _)).add_right ((hc _ _).add_left (hc _ _))
  obtain ⟨S, hS⟩ := hss
  refine ⟨S, fun Φ hΦ p => ?_⟩
  have h0 : π (aeval LZ (∏ v ∈ S, (X - C v))) = 0 := by
    rw [← Polynomial.aeval_algHom_apply]; exact hS
  have h2 := piQ_eq_zero V I h0 Φ hΦ
  have e : (aeval LZ (∏ v ∈ S, (X - C v))).1 = aeval (lie E (r + s) (Zr (r + s) r)) (∏ v ∈ S, (X - C v)) := by
    rw [← hLZ]
    exact (Polynomial.aeval_algHom_apply (Pa V I).val LZ _).symm
  rw [← e]
  exact h2.2 p

end Key2

section Final

variable (r s : ℕ) (m : (E →+* ℂ) → Multiset ℂ)

/- English proof (translation)
Rewrite using `[aeval_def, eval₂_eq_sum, Polynomial.sum, Polynomial.sum, LinearMap.sum_apply, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Module.End.mul_apply, Module.algebraMap_end_apply]`. Both sides reduce to the same expression.
-/
theorem aeval_apply_val {N : ℕ} (T : Module.End ℂ (Sm E N)) (q : ℂ[X]) (Φ : Sm E N) (x : GA E N) :
    (aeval T q Φ).1 x = q.sum fun k a => a * ((T ^ k) Φ).1 x := by
  rw [aeval_def, eval₂_eq_sum, Polynomial.sum, Polynomial.sum, LinearMap.sum_apply,
    AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Module.End.mul_apply, Module.algebraMap_end_apply]
  rfl

/- English proof (translation)
Take `⟨-, -, -, hD⟩` from `dict_holds E (r + s)`. Establish `hCT` using `(hD ψ hψ r hr (by omega)).1`. Set `_ : MeasurableSpace (BlockIx (r + s) r → Ad E)` to `borel _`. Establish `_ : BorelSpace (BlockIx (r + s) r → Ad E)` using `⟨rfl⟩`. Take `⟨μ, 𝓕, hμ, h𝓕, hct⟩` from `hCT`.

Take `⟨F, hF1, -⟩` from `GlobalTheory.CompanionTheory.CTSmooth.ct_smooth E (r + s) r ψ hψ.left hψ.level μ 𝓕 hμ h𝓕`. Establish `hlie : ∀ φ F' : Sm E (r + s), (∀ (γ : GL (Fin (r + s)) E) (g : GA E (r + s)), φ.1 (ratGL E (r + s) γ * g) = φ.1 g) → IsOpen {k | finRep E (r + s) k φ = φ} → (∀ g, F'.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) → ∀ (X : Lie E (r + s)) (g : GA E (r + s)), (lie E (r + s) X F').1 g = ∫ x in …`. Introduce `φ F' h1 h2 h3 X g`. Take `⟨F'', h4, h5⟩` from `GlobalTheory.CompanionTheory.CTSmooth.ct_smooth E (r + s) r φ h1 h2 μ 𝓕 hμ h𝓕`. Establish `e : F' = F''` using `Subtype.ext (funext fun g => (h3 g).trans (h4 g).symm)`.

Rewrite using `[e]`. Conclude with `h5 X g`. Use `⟨F, funext fun g => by rw [hF1, hct]; rfl, fun x g => ?_, fun τ u => ?_⟩` and prove the remaining obligations. Rewrite using `[hF1, hF1]`. Conclude with `GlobalTheory.T.constant_term_translate_formula E (r + s) r ψ hψ.left hψ.level μ 𝓕 hμ h𝓕 x g`.

Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations. Establish `hz : cap τ u ∈ Zalg E (r + s)` using `Algebra.subset_adjoin ⟨τ, u, rfl⟩`. Establish `h1` using `GlobalTheory.T.constant_term_automorphic_criterion E (r + s) r μ 𝓕 hμ h𝓕 hlie ψ F hψ.left hψ.level hF1 (cap τ u) hz g`. Rewrite `h1` using `[(hinf τ).2 u ψ (Submodule.mem_span_singleton_self ψ)]`. Rewrite using `[h1]`.

Simplify using `only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[integral_const_mul, hF1]`.
-/
theorem ct_mem (hr : 0 < r) (hs : 0 < s) (ψ : Sm E (r + s)) (hψ : IsAutForm ψ)
    (hinf : ∀ τ, HasInfCharGL (Submodule.span ℂ {ψ}) τ (m τ)) :
    ∃ F : Sm E (r + s), F.1 = An.ctn r ψ.1 ∧ F ∈ Vsp r s m := by
  obtain ⟨-, -, -, hD⟩ := dict_holds E (r + s)
  have hCT := (hD ψ hψ r hr (by omega)).1
  let _ : MeasurableSpace (BlockIx (r + s) r → Ad E) := borel _
  have _ : BorelSpace (BlockIx (r + s) r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, hct⟩ := hCT
  obtain ⟨F, hF1, -⟩ := GlobalTheory.CompanionTheory.CTSmooth.ct_smooth E (r + s) r ψ hψ.left hψ.level μ 𝓕 hμ h𝓕
  have hlie : ∀ φ F' : Sm E (r + s), (∀ (γ : GL (Fin (r + s)) E) (g : GA E (r + s)), φ.1 (ratGL E (r + s) γ * g) = φ.1 g) →
      IsOpen {k | finRep E (r + s) k φ = φ} → (∀ g, F'.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) →
      ∀ (X : Lie E (r + s)) (g : GA E (r + s)), (lie E (r + s) X F').1 g = ∫ x in 𝓕, (lie E (r + s) X φ).1 (unip x * g) ∂μ := by
    intro φ F' h1 h2 h3 X g
    obtain ⟨F'', h4, h5⟩ := GlobalTheory.CompanionTheory.CTSmooth.ct_smooth E (r + s) r φ h1 h2 μ 𝓕 hμ h𝓕
    have e : F' = F'' := Subtype.ext (funext fun g => (h3 g).trans (h4 g).symm)
    rw [e]
    exact h5 X g
  refine ⟨F, funext fun g => by rw [hF1, hct]; rfl, fun x g => ?_, fun τ u => ?_⟩
  · rw [hF1, hF1]
    exact GlobalTheory.T.constant_term_translate_formula E (r + s) r ψ hψ.left hψ.level μ 𝓕 hμ h𝓕 x g
  · refine Subtype.ext (funext fun g => ?_)
    have hz : cap τ u ∈ Zalg E (r + s) := Algebra.subset_adjoin ⟨τ, u, rfl⟩
    have h1 := GlobalTheory.T.constant_term_automorphic_criterion E (r + s) r μ 𝓕 hμ h𝓕 hlie ψ F hψ.left hψ.level hF1 (cap τ u) hz g
    rw [(hinf τ).2 u ψ (Submodule.mem_span_singleton_self ψ)] at h1
    rw [h1]
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, hF1]

/- English proof (translation)
Use `⟨fun x g => ?_, fun τ u => ?_⟩` and prove the remaining obligations. Simplify using `only [rt_apply]`. Rewrite using `[mul_assoc, hF.1]`. Establish `hcomm : Commute (cap τ u) (rt E (r + s) (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g'))`. Rewrite using `[map_mul]`.

Conclude with `(GlobalTheory.CapAdInv.cap_commute_rt_infGL E _ τ u _).mul_right (commute_cap_finRep τ u g')`. Rewrite using `[← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply, hF.2, map_smul]`.
-/
theorem rt_mem {F : Sm E (r + s)} (hF : F ∈ Vsp r s m) (k : Kinf E (r + s)) (g' : GL (Fin (r + s)) (Af E)) :
    rt E (r + s) (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g') F ∈ Vsp r s m := by
  refine ⟨fun x g => ?_, fun τ u => ?_⟩
  · simp only [rt_apply]
    rw [mul_assoc, hF.1]
  · have hcomm : Commute (cap τ u) (rt E (r + s) (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g')) := by
      rw [map_mul]
      exact (GlobalTheory.CapAdInv.cap_commute_rt_infGL E _ τ u _).mul_right (commute_cap_finRep τ u g')
    rw [← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply, hF.2, map_smul]

/- English proof (translation)
Rewrite using `[aT, aInf_zero', map_one]`.
-/
theorem aT_zero' (N : ℕ) : aT E N r 0 = 1 := by
  rw [aT, aInf_zero', map_one]

/- English proof (translation)
Take `⟨S, hS⟩` from `key r s m hm`. Take `⟨L, hL⟩` from `ode_decomp S`. Use `set Z := lie E (r + s) (Zr (r + s) r) with hZ`. Set `G : ℂ → GA E (r + s) → ℂ` to `fun v g => pev (L v) (fun k t => iteratedDeriv k (fun t : ℝ => F.1 (aT E (r + s) r t * g)) t) 0`. Establish `hseq : ∀ Φ ∈ Vsp r s m, ∀ p : GA E r × GA E s, (∀ k t, HasDerivAt (fun t : ℝ => ((Z ^ k) Φ).1 (lev (Ad E) r s p * aT E (r + s) r t)) (((Z ^ (k + 1)) Φ).1 (lev (Ad E) r s p * aT E (r + s) r t)) t) ∧ ∀ t, pev (∏ v ∈ S, (X - C v)) (fun k t => ((Z ^ k) Φ).1 (lev (Ad E) r s p * aT E ( …`.

Introduce `Φ hΦ p`. Use `⟨fun k t => ?_, fun t => ?_⟩` and prove the remaining obligations. Establish `h` using `hasDerivAt_aT r s ((Z ^ k) Φ) (lev (Ad E) r s p) t`. Rewrite using `[pow_succ', Module.End.mul_apply]` and apply the resulting hypothesis. Take `⟨p', hp'⟩` from `lev_mul_aT r s p t`.

Establish `h` using `hS Φ hΦ p'`. Rewrite `h` using `[aeval_apply_val, ← hp']`. Conclude with `h`. Establish `hrep : ∀ g : GA E (r + s), ∃ Φ ∈ Vsp r s m, ∃ p : GA E r × GA E s, ∀ t, F.1 (aT E (r + s) r t * g) = Φ.1 (lev (Ad E) r s p * aT E (r + s) r t)`. Introduce `g`.

Take `⟨x, p, k, g', rfl⟩` from `iwasawa2 r s g`. Use `⟨_, rt_mem r s m hF k g', p, fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[aT_mul_decomp r s F.1 hF.1 x p _ t, rt_apply]`. Establish `hiter : ∀ g (s₀ : ℝ), ∃ f : ℕ → ℝ → ℂ, (∀ k t, HasDerivAt (f k) (f (k + 1) t) t) ∧ (∀ t, pev (∏ v ∈ S, (X - C v)) f t = 0) ∧ (fun k t => iteratedDeriv k (fun t : ℝ => F.1 (aT E (r + s) r t * (aT E (r + s) r s₀ * g))) t) = (fun k t => f k (t + s₀)) ∧ (fun k t => iteratedDeriv k (f …`. Introduce `g s₀`.

Take `⟨Φ, hΦ, p, hrepg⟩` from `hrep g`. Take `⟨hf, hq⟩` from `hseq Φ hΦ p`. Use `set f : ℕ → ℝ → ℂ := fun k t => ((Z ^ k) Φ).1 (lev (Ad E) r s p * aT E (r + s) r t) with hfdef`. Establish `h0 : (fun t : ℝ => F.1 (aT E (r + s) r t * g)) = f 0` using `funext fun t => by`. Rewrite using `[hrepg t]`.

Simplify using `[f]`. Establish `h0' : (fun t : ℝ => F.1 (aT E (r + s) r t * (aT E (r + s) r s₀ * g))) = fun t => f 0 (t + s₀)`. Use function extensionality and compare the values at `fun t => by`. Rewrite using `[← mul_assoc, ← aT_add', hrepg]`. Simplify using `[f]`.

Establish `hf' : ∀ k t, HasDerivAt (fun t => f k (t + s₀)) (f (k + 1) (t + s₀)) t` using `fun k t => (hf k (t + s₀)).comp_add_const t s₀`. Use `⟨f, hf, hq, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k t`. Rewrite using `[h0']`. Conclude with `congrFun (iteratedDeriv_chain (fun k t => f k (t + s₀)) hf' k) t`.

Use function extensionality and compare the values at `k t`. Rewrite using `[h0]`. Conclude with `congrFun (iteratedDeriv_chain f hf k) t`. Use `⟨S, G, funext fun g => ?_, fun v hv t g => ?_⟩` and prove the remaining obligations. Take `⟨f, hf, hq, -, hfe⟩` from `hiter g 0`.

Establish `e0 : F.1 g = f 0 0`. Rewrite using `[← hfe]`. Simplify using `only [iteratedDeriv_zero, aT_zero', one_mul]`. Rewrite using `[Finset.sum_apply, e0, ((hL f hf hq).1 0)]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations.

Simplify using `only [G, hfe]`. Take `⟨f, hf, hq, hfs, hfe⟩` from `hiter g t`. Establish `e1 : G v (aT E (r + s) r t * g) = pev (L v) f t`. Simplify using `only [G]`. Rewrite using `[hfs]`.

Simplify using `only [pev, zero_add]`. Establish `e2 : G v g = pev (L v) f 0`. Simplify using `only [G, hfe]`. Rewrite using `[e1, e2, (hL f hf hq).2 v hv t]`.
-/
theorem expDec_of (hm : ∀ τ, (m τ).Nodup ∧ Multiset.card (m τ) = r + s) (F : Sm E (r + s)) (hF : F ∈ Vsp r s m) :
    ∃ (C : Finset ℂ) (G : ℂ → GA E (r + s) → ℂ), F.1 = ∑ c ∈ C, G c ∧
      ∀ c ∈ C, ∀ (t : ℝ) g, G c (aT E (r + s) r t * g) = Complex.exp (c * t) * G c g := by
  classical
  obtain ⟨S, hS⟩ := key r s m hm
  obtain ⟨L, hL⟩ := ode_decomp S
  set Z := lie E (r + s) (Zr (r + s) r) with hZ
  let G : ℂ → GA E (r + s) → ℂ := fun v g =>
    pev (L v) (fun k t => iteratedDeriv k (fun t : ℝ => F.1 (aT E (r + s) r t * g)) t) 0

  have hseq : ∀ Φ ∈ Vsp r s m, ∀ p : GA E r × GA E s,
      (∀ k t, HasDerivAt (fun t : ℝ => ((Z ^ k) Φ).1 (lev (Ad E) r s p * aT E (r + s) r t))
        (((Z ^ (k + 1)) Φ).1 (lev (Ad E) r s p * aT E (r + s) r t)) t) ∧
      ∀ t, pev (∏ v ∈ S, (X - C v)) (fun k t => ((Z ^ k) Φ).1 (lev (Ad E) r s p * aT E (r + s) r t)) t = 0 := by
    intro Φ hΦ p
    refine ⟨fun k t => ?_, fun t => ?_⟩
    · have h := hasDerivAt_aT r s ((Z ^ k) Φ) (lev (Ad E) r s p) t
      rwa [pow_succ', Module.End.mul_apply]
    · obtain ⟨p', hp'⟩ := lev_mul_aT r s p t
      have h := hS Φ hΦ p'
      rw [aeval_apply_val, ← hp'] at h
      exact h

  have hrep : ∀ g : GA E (r + s), ∃ Φ ∈ Vsp r s m, ∃ p : GA E r × GA E s,
      ∀ t, F.1 (aT E (r + s) r t * g) = Φ.1 (lev (Ad E) r s p * aT E (r + s) r t) := by
    intro g
    obtain ⟨x, p, k, g', rfl⟩ := iwasawa2 r s g
    refine ⟨_, rt_mem r s m hF k g', p, fun t => ?_⟩
    rw [aT_mul_decomp r s F.1 hF.1 x p _ t, rt_apply]
  have hiter : ∀ g (s₀ : ℝ), ∃ f : ℕ → ℝ → ℂ, (∀ k t, HasDerivAt (f k) (f (k + 1) t) t) ∧
      (∀ t, pev (∏ v ∈ S, (X - C v)) f t = 0) ∧
      (fun k t => iteratedDeriv k (fun t : ℝ => F.1 (aT E (r + s) r t * (aT E (r + s) r s₀ * g))) t) =
        (fun k t => f k (t + s₀)) ∧
      (fun k t => iteratedDeriv k (fun t : ℝ => F.1 (aT E (r + s) r t * g)) t) = f := by
    intro g s₀
    obtain ⟨Φ, hΦ, p, hrepg⟩ := hrep g
    obtain ⟨hf, hq⟩ := hseq Φ hΦ p
    set f : ℕ → ℝ → ℂ := fun k t => ((Z ^ k) Φ).1 (lev (Ad E) r s p * aT E (r + s) r t) with hfdef
    have h0 : (fun t : ℝ => F.1 (aT E (r + s) r t * g)) = f 0 := funext fun t => by
      rw [hrepg t]; simp [f]
    have h0' : (fun t : ℝ => F.1 (aT E (r + s) r t * (aT E (r + s) r s₀ * g))) = fun t => f 0 (t + s₀) :=
      funext fun t => by
        rw [← mul_assoc, ← aT_add', hrepg]; simp [f]
    have hf' : ∀ k t, HasDerivAt (fun t => f k (t + s₀)) (f (k + 1) (t + s₀)) t := fun k t =>
      (hf k (t + s₀)).comp_add_const t s₀
    refine ⟨f, hf, hq, ?_, ?_⟩
    · funext k t
      rw [h0']
      exact congrFun (iteratedDeriv_chain (fun k t => f k (t + s₀)) hf' k) t
    · funext k t
      rw [h0]
      exact congrFun (iteratedDeriv_chain f hf k) t
  refine ⟨S, G, funext fun g => ?_, fun v hv t g => ?_⟩
  · obtain ⟨f, hf, hq, -, hfe⟩ := hiter g 0
    have e0 : F.1 g = f 0 0 := by
      rw [← hfe]
      simp only [iteratedDeriv_zero, aT_zero', one_mul]
    rw [Finset.sum_apply, e0, ((hL f hf hq).1 0)]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [G, hfe]
  · obtain ⟨f, hf, hq, hfs, hfe⟩ := hiter g t
    have e1 : G v (aT E (r + s) r t * g) = pev (L v) f t := by
      simp only [G]
      rw [hfs]
      simp only [pev, zero_add]
    have e2 : G v g = pev (L v) f 0 := by
      simp only [G, hfe]
    rw [e1, e2, (hL f hf hq).2 v hv t]

end Final

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

/- English proof (translation)
Introduce `E _ _ _ N r ψ hψ _ hinf hr hrN`. Take `⟨s, rfl⟩ : ∃ s, N = r + s` from `⟨N - r, by omega⟩`. Use `choose m hm1 hm2 using hinf`. Take `⟨F, hF1, hF2⟩` from `NoLogarithmTerms.ct_mem r s m hr (by omega) ψ hψ hm1`. Take `⟨C, G, h1, h2⟩` from `NoLogarithmTerms.expDec_of r s m (fun τ => ⟨hm2 τ, (hm1 τ).1⟩) F hF2`.

Conclude with `⟨C, G, hF1 ▸ h1, h2⟩`.
-/
theorem noLog_holds : NoLog := by
  intro E _ _ _ N r ψ hψ _ hinf hr hrN
  obtain ⟨s, rfl⟩ : ∃ s, N = r + s := ⟨N - r, by omega⟩
  choose m hm1 hm2 using hinf
  obtain ⟨F, hF1, hF2⟩ := NoLogarithmTerms.ct_mem r s m hr (by omega) ψ hψ hm1
  obtain ⟨C, G, h1, h2⟩ := NoLogarithmTerms.expDec_of r s m (fun τ => ⟨hm2 τ, (hm1 τ).1⟩) F hF2
  exact ⟨C, G, hF1 ▸ h1, h2⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

end
