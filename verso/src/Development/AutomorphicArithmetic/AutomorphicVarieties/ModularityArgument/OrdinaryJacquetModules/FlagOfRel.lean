import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.FlagJ
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.RelKill
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Factor
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.RegArith
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LemmaL
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MapApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.IrrIffSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord

/- English proof (translation)
Set `z : MonoidAlgebra K H` to `MonoidAlgebra.of K H s`. Establish `hlz : ∀ i, MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z = ((ψ i s : Kˣ) : K)` using `fun i => by`. Simplify using `only [z, MonoidAlgebra.lift_of]`. Both sides reduce to the same expression. Establish `hPz : MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r) z = W.mat r s`.

Simplify using `only [z, MonoidAlgebra.lift_of]`. Both sides reduce to the same expression. Establish `hext` using `AlgebraTools.ord_ext (R := K) ((Units.coeHom (Matrix (Fin n) (Fin n) K)).comp r) (fun i => (Units.coeHom K).comp (ψ i)) h0`. Establish `hz : ∀ i j, i ≠ j → IsUnit (MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z - MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ j)) z)` using `fun i j hij => by`. Rewrite using `[hlz, hlz]`.

Conclude with `(sub_ne_zero.2 fun e => hij (hs (Units.ext e))).isUnit`. Take `⟨hc, hlow, hdiag⟩` from `AlgebraTools.lag_triangular (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r)) (fun i => MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i))) z hext hz`. Establish `hne` using `AlgebraTools.lag_ne_zero (fun i => MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z) (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r) z) hz (by`. Rewrite using `[hPz, hch, Polynomial.map_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hlz]`. Use the proof step `simp)`. Take `⟨g, hg⟩` from `AlgebraTools.coi_conj_single _ hc hne`. Use `⟨g, fun t => ?_⟩` and prove the remaining obligations. Use `set f := AlgebraTools.lag (fun i => MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z) (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r) z) with hf`.

Establish `ent : ∀ (M : Matrix (Fin n) (Fin n) K) a b, (Matrix.single a a (1 : K) * M * Matrix.single b b (1 : K) : Matrix (Fin n) (Fin n) K) a b = M a b` using `fun M a b => by`. Simplify using the standard rewrite rules. Establish `key : ∀ a b, (g * r t * g⁻¹ : GL (Fin n) K) a b = ((g : Matrix (Fin n) (Fin n) K) * (f a * (r t : Matrix (Fin n) (Fin n) K) * f b) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) a b`. Introduce `a b`. Rewrite using `[← ent ((g * r t * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b, ← hg a, ← hg b]`.

Simplify using `only [Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]`. Use `⟨fun i j hji => ?_, fun i => ?_⟩` and prove the remaining obligations. Establish `h` using `hlow (MonoidAlgebra.of K H t) i j hji`. Rewrite `h` using `[MonoidAlgebra.lift_of]`. Establish `h' : f i * (r t : Matrix (Fin n) (Fin n) K) * f j = 0` using `h`.

Rewrite using `[key, h']`. Simplify using the standard rewrite rules. Establish `h` using `hdiag (MonoidAlgebra.of K H t) i`. Simplify using `only [MonoidAlgebra.lift_of] at h`. Establish `h' : f i * (r t : Matrix (Fin n) (Fin n) K) * f i = (ψ i t : K) • f i` using `h`.

Rewrite using `[key, h', Matrix.mul_smul, Matrix.smul_mul, hg i]`. Simplify using the standard rewrite rules.
-/
private theorem flag_of_rel {K H : Type} [Field K] [Group H] {n : ℕ} (r : H →* GL (Fin n) K) (ψ : Fin n → H →* Kˣ)
    (h0 : ∀ g : Fin n → H, (List.ofFn fun i => ((r (g i) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) -
      algebraMap K _ ((ψ i (g i) : Kˣ) : K)).prod = 0)
    (hch : ∀ t, (W.mat r t).charpoly = ∏ i, (X - C ((ψ i t : Kˣ) : K)))
    (s : H) (hs : Function.Injective fun i => ψ i s) : W.HasFlag r ψ := by
  classical
  let z : MonoidAlgebra K H := MonoidAlgebra.of K H s
  have hlz : ∀ i, MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z = ((ψ i s : Kˣ) : K) := fun i => by
    simp only [z, MonoidAlgebra.lift_of]
    rfl
  have hPz : MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r) z = W.mat r s := by
    simp only [z, MonoidAlgebra.lift_of]
    rfl
  have hext := AlgebraTools.ord_ext (R := K) ((Units.coeHom (Matrix (Fin n) (Fin n) K)).comp r)
    (fun i => (Units.coeHom K).comp (ψ i)) h0
  have hz : ∀ i j, i ≠ j → IsUnit (MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z -
      MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ j)) z) := fun i j hij => by
    rw [hlz, hlz]
    exact (sub_ne_zero.2 fun e => hij (hs (Units.ext e))).isUnit
  obtain ⟨hc, hlow, hdiag⟩ := AlgebraTools.lag_triangular
    (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r))
    (fun i => MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i))) z hext hz
  have hne := AlgebraTools.lag_ne_zero (fun i => MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z)
    (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r) z) hz (by
      rw [hPz, hch, Polynomial.map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hlz]
      simp)
  obtain ⟨g, hg⟩ := AlgebraTools.coi_conj_single _ hc hne
  refine ⟨g, fun t => ?_⟩
  set f := AlgebraTools.lag (fun i => MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z)
    (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r) z) with hf
  have ent : ∀ (M : Matrix (Fin n) (Fin n) K) a b,
      (Matrix.single a a (1 : K) * M * Matrix.single b b (1 : K) : Matrix (Fin n) (Fin n) K) a b = M a b := fun M a b => by
    simp
  have key : ∀ a b, (g * r t * g⁻¹ : GL (Fin n) K) a b =
      ((g : Matrix (Fin n) (Fin n) K) * (f a * (r t : Matrix (Fin n) (Fin n) K) * f b) *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) a b := by
    intro a b
    rw [← ent ((g * r t * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b, ← hg a, ← hg b]
    simp only [Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · have h := hlow (MonoidAlgebra.of K H t) i j hji
    rw [MonoidAlgebra.lift_of] at h
    have h' : f i * (r t : Matrix (Fin n) (Fin n) K) * f j = 0 := h
    rw [key, h']
    simp
  · have h := hdiag (MonoidAlgebra.of K H t) i
    simp only [MonoidAlgebra.lift_of] at h
    have h' : f i * (r t : Matrix (Fin n) (Fin n) K) * f i = (ψ i t : K) • f i := h
    rw [key, h', Matrix.mul_smul, Matrix.smul_mul, hg i]
    simp

/- English proof (translation)
Express the relevant statement in the definitionally equal form `D.D A[X] (MonoidAlgebra.mapDomainRingHom A[X] φ _) = D.D A[X] _`. Use `congr 1`. Rewrite using `[map_sub]`. Simplify using the standard rewrite rules.
-/
private theorem chi_single {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (h : H) : (D.comap φ).chi (MonoidAlgebra.single h 1) = D.chi (MonoidAlgebra.single (φ h) 1) := by
  change D.D A[X] (MonoidAlgebra.mapDomainRingHom A[X] φ _) = D.D A[X] _
  congr 1
  rw [map_sub]
  simp

/- English proof (translation)
Establish `hchi : ∀ h, D.chi (MonoidAlgebra.single (φ h) 1) = (W.GDet.ofRep (W.mat ρ)).chi (MonoidAlgebra.single h 1)` using `fun h => by rw [← hD, chi_single]`. Establish `hker : φ.ker ≤ ρ.ker` using `fun g hg => by`. Establish `h0` using `(Ws.Eb.trPlus ρ hF).1 (MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 1) fun h => by`. Establish `e : (W.GDet.ofRep (W.mat ρ)).tr (MonoidAlgebra.single (h * g) 1) = (W.GDet.ofRep (W.mat ρ)).tr (MonoidAlgebra.single h 1)`. Unfold `W.GDet.tr W.GDet.lam`.

Rewrite using `[← hchi, ← hchi, map_mul, MonoidHom.mem_ker.1 hg, mul_one]`. Rewrite `e` using `[(AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn, (AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn]`. Rewrite using `[(AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn, mul_sub, map_sub, Matrix.trace_sub, MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, mul_one, mul_one, e, sub_self]`. Rewrite `h0` using `[map_sub, sub_eq_zero]`. Use `Units.ext ?_` and prove the remaining obligations.

Simplify `h0` using `[W.GDet.repAlg, W.mat]`. Set `ρ₀ : G →* GL (Fin n) A` to `φ.liftOfSurjective hφ ⟨ρ, hker⟩`. Establish `h0 : ∀ h, ρ₀ (φ h) = ρ h` using `fun h => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ h`. Establish `hm : ∀ h, W.mat ρ₀ (φ h) = W.mat ρ h` using `fun h => congrArg Units.val (h0 h)`. Use `⟨ρ₀, MonoidHom.ext h0, ?_, CA.d_gext _ _ fun g i _ _ => ?_⟩` and prove the remaining obligations.

Use `top_le_iff.1 (le_trans (le_of_eq (Eq.symm hF)) (Submodule.span_mono ?_))` and prove the remaining obligations. Introduce and unpack `_ ⟨h, rfl⟩`. Conclude with `⟨φ h, hm h⟩`. Take `⟨h, rfl⟩` from `hφ g`. Unfold `W.GDet.lam`.

Rewrite using `[hchi, (AlgebraTools.Det.repApi _).2.1, (AlgebraTools.Det.repApi _).2.1, hm]`.
-/
private theorem descend {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (hφ : Function.Surjective φ) (ρ : H →* GL (Fin n) A) (hn : 1 ≤ n) (hF : Ws.Eb.Full ρ)
    (hD : D.comap φ = W.GDet.ofRep (W.mat ρ)) :
    ∃ ρ₀ : G →* GL (Fin n) A, ρ₀.comp φ = ρ ∧ Ws.Eb.Full ρ₀ ∧ D = W.GDet.ofRep (W.mat ρ₀) := by
  have hchi : ∀ h, D.chi (MonoidAlgebra.single (φ h) 1) = (W.GDet.ofRep (W.mat ρ)).chi (MonoidAlgebra.single h 1) :=
    fun h => by rw [← hD, chi_single]
  have hker : φ.ker ≤ ρ.ker := fun g hg => by
    have h0 := (Ws.Eb.trPlus ρ hF).1 (MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 1) fun h => by
      have e : (W.GDet.ofRep (W.mat ρ)).tr (MonoidAlgebra.single (h * g) 1) =
          (W.GDet.ofRep (W.mat ρ)).tr (MonoidAlgebra.single h 1) := by
        unfold W.GDet.tr W.GDet.lam
        rw [← hchi, ← hchi, map_mul, MonoidHom.mem_ker.1 hg, mul_one]
      rw [(AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn, (AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn] at e
      rw [(AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn, mul_sub, map_sub, Matrix.trace_sub,
        MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, mul_one, mul_one, e, sub_self]
    rw [map_sub, sub_eq_zero] at h0
    refine Units.ext ?_
    simpa [W.GDet.repAlg, W.mat] using h0
  let ρ₀ : G →* GL (Fin n) A := φ.liftOfSurjective hφ ⟨ρ, hker⟩
  have h0 : ∀ h, ρ₀ (φ h) = ρ h := fun h => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ h
  have hm : ∀ h, W.mat ρ₀ (φ h) = W.mat ρ h := fun h => congrArg Units.val (h0 h)
  refine ⟨ρ₀, MonoidHom.ext h0, ?_, CA.d_gext _ _ fun g i _ _ => ?_⟩
  · refine top_le_iff.1 (le_trans (le_of_eq (Eq.symm hF)) (Submodule.span_mono ?_))
    rintro _ ⟨h, rfl⟩
    exact ⟨φ h, hm h⟩
  · obtain ⟨h, rfl⟩ := hφ g
    unfold W.GDet.lam
    rw [hchi, (AlgebraTools.Det.repApi _).2.1, (AlgebraTools.Det.repApi _).2.1, hm]

/- English proof (translation)
Introduce `H l _ L Ω _ _ _ _ _ _ s n V c r B Λ J hJ x h ρ hJx hA hx hirr v`. Establish `hn : 1 ≤ n`. Break down `Nat.eq_zero_or_pos n with rfl | h0` into its components or cases. Conclude with `absurd (Subsingleton.elim _ _) hirr.1`. Conclude with `h0`.

Establish `hs : Function.Surjective V.pr` using `fun g => by`. Take `⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1` from `QuotientGroup.mk_surjective g.1`. Take `⟨σ, rfl⟩` from `(V.hη τ).1 (by rw [hτ]; exact g.2)`. Conclude with `⟨σ, Subtype.ext hτ⟩`. Establish `hF : Ws.Eb.Full ρ` using `(AlgebraTools.Det.irrIffSpan (W.mat ρ)).1 fun N hN => by`.

Break down `hirr.2.2 N le_top fun g v hv => hN g v hv with h1 | h1` into its components or cases. Conclude with `Or.inl h1`. Conclude with `Or.inr h1`. Take `⟨ρ₀, rfl, hfull, hD⟩` from `descend x.D V.pr hs ρ hn hF hx`. Take `⟨hO, -⟩` from `Ws.Eb.relKill B x ρ₀ hfull hD`.

Take `⟨g₀, hg₀⟩` from `Th.Nm.regArith H s h v (x.psi v) hA.1 (hA.2 v)`. Use `flag_of_rel _ (x.psi v) (hO v) (fun t => ?_) g₀ hg₀` and prove the remaining obligations. Set `xb : B.B ⧸ J →+* Qbar l` to `Ideal.Quotient.lift J (x : B.B →+* Qbar l) fun a ha => hJx ha`. Establish `e0 : xb.comp (Ideal.Quotient.mk J) = (x : B.B →+* Qbar l)` using `RingHom.ext fun a => rfl`. Establish `e1 : (B.DD J).map xb = W.GDet.ofRep (W.mat ρ₀)`.

Establish `h1 : (B.DD J).map xb = B.u.D.map (xb.comp (Ideal.Quotient.mk J))` using `(CA.d_gmap B.u.D).2.1 _ _`. Rewrite using `[h1, e0]`. Conclude with `hD`. Establish `e2` using `(AlgebraTools.Det.mapApi (B.DD J) xb).1 (MonoidAlgebra.single (V.frame.φ v t) 1)`. Rewrite `e2` using `[MonoidAlgebra.mapRingHom_single, map_one, e1, (AlgebraTools.Det.repApi _).2.1]`.

Use `e2.trans ((congrArg (Polynomial.map xb) (hJ.O1 v t)).trans ?_)` and prove the remaining obligations. Rewrite using `[Polynomial.map_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Z.Ord.flagJ :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → FlagJ := by
  intro H l _ L Ω _ _ _ _ _ _ s n V c r B Λ J hJ x h ρ hJx hA hx hirr v
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h0
    · exact absurd (Subsingleton.elim _ _) hirr.1
    · exact h0
  have hs : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨σ, Subtype.ext hτ⟩
  have hF : Ws.Eb.Full ρ := (AlgebraTools.Det.irrIffSpan (W.mat ρ)).1 fun N hN => by
    rcases hirr.2.2 N le_top fun g v hv => hN g v hv with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  obtain ⟨ρ₀, rfl, hfull, hD⟩ := descend x.D V.pr hs ρ hn hF hx
  obtain ⟨hO, -⟩ := Ws.Eb.relKill B x ρ₀ hfull hD
  obtain ⟨g₀, hg₀⟩ := Th.Nm.regArith H s h v (x.psi v) hA.1 (hA.2 v)
  refine flag_of_rel _ (x.psi v) (hO v) (fun t => ?_) g₀ hg₀
  let xb : B.B ⧸ J →+* Qbar l := Ideal.Quotient.lift J (x : B.B →+* Qbar l) fun a ha => hJx ha
  have e0 : xb.comp (Ideal.Quotient.mk J) = (x : B.B →+* Qbar l) := RingHom.ext fun a => rfl
  have e1 : (B.DD J).map xb = W.GDet.ofRep (W.mat ρ₀) := by
    have h1 : (B.DD J).map xb = B.u.D.map (xb.comp (Ideal.Quotient.mk J)) := (CA.d_gmap B.u.D).2.1 _ _
    rw [h1, e0]
    exact hD
  have e2 := (AlgebraTools.Det.mapApi (B.DD J) xb).1 (MonoidAlgebra.single (V.frame.φ v t) 1)
  rw [MonoidAlgebra.mapRingHom_single, map_one, e1, (AlgebraTools.Det.repApi _).2.1] at e2
  refine e2.trans ((congrArg (Polynomial.map xb) (hJ.O1 v t)).trans ?_)
  rw [Polynomial.map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rfl
