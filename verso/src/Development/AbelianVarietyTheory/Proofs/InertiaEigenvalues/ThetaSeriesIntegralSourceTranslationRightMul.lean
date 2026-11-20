import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionTrivialOffSupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ExportSeries.DualType

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SourceTrans

variable {D : D7}

/- English proof (translation)
Establish `he : idemAt PP * idemAt PP = idemAt PP` using `(hQ.isIdemAt hP).1.1`. Establish `h1 : idem Q * idemAt PP = idemAt PP`. Rewrite using `[idem, Finset.sum_mul, Finset.sum_eq_single PP (fun q hq hne => hQ.mul_eq_zero hq hP (Ne.symm hne)) (fun h => absurd hP h), he]`. Establish `h2 : idem Q * cA D (idemAt PP) = 0`. Rewrite using `[idem, Finset.sum_mul]`.

Conclude with `Finset.sum_eq_zero fun q hq => hQ.mul_conj hq hP`. Establish `h3 : cA D (idem Q) * idemAt PP = 0`. Rewrite using `[idem, map_sum, Finset.sum_mul]`. Conclude with `Finset.sum_eq_zero fun q hq => by rw [mul_comm]; exact hQ.mul_conj hP hq`. Establish `h4 : cA D (idem Q) * cA D (idemAt PP) = cA D (idemAt PP)` using `by rw [← map_mul, h1]`.

Rewrite using `[add_mul, mul_add, mul_add, h1, h2, h3, h4, add_zero, zero_add]`.
-/
theorem idem_mul_idemAt {Q : Finset (Pl D.host.E)} (hQ : SplitSet Q) {PP : Pl D.host.E} (hP : PP ∈ Q) :
    (idem Q + cA D (idem Q)) * (idemAt PP + cA D (idemAt PP)) = idemAt PP + cA D (idemAt PP) := by
  have he : idemAt PP * idemAt PP = idemAt PP := (hQ.isIdemAt hP).1.1
  have h1 : idem Q * idemAt PP = idemAt PP := by
    rw [idem, Finset.sum_mul, Finset.sum_eq_single PP (fun q hq hne => hQ.mul_eq_zero hq hP (Ne.symm hne))
      (fun h => absurd hP h), he]
  have h2 : idem Q * cA D (idemAt PP) = 0 := by
    rw [idem, Finset.sum_mul]
    exact Finset.sum_eq_zero fun q hq => hQ.mul_conj hq hP
  have h3 : cA D (idem Q) * idemAt PP = 0 := by
    rw [idem, map_sum, Finset.sum_mul]
    exact Finset.sum_eq_zero fun q hq => by rw [mul_comm]; exact hQ.mul_conj hP hq
  have h4 : cA D (idem Q) * cA D (idemAt PP) = cA D (idemAt PP) := by rw [← map_mul, h1]
  rw [add_mul, mul_add, mul_add, h1, h2, h3, h4, add_zero, zero_add]

/- English proof (translation)
Introduce `i j`. Rewrite using `[← h i j, ← mul_assoc, idem_mul_idemAt hQ hP]`.
-/
theorem suppAt_idem_of {Q : Finset (Pl D.host.E)} (hQ : SplitSet Q) {PP : Pl D.host.E} (hP : PP ∈ Q) {V : HSp D}
    {g : GA D V} (h : SuppAt (idemAt PP) V g) : SuppAt (idem Q) V g := by
  intro i j
  rw [← h i j, ← mul_assoc, idem_mul_idemAt hQ hP]

/- English proof (translation)
Rewrite using `[idem, Finset.sum_singleton]`. Conclude with `h`.
-/
theorem suppAt_single {PP : Pl D.host.E} {V : HSp D} {g : GA D V} (h : SuppAt (idemAt PP) V g) :
    SuppAt (idem {PP}) V g := by
  rw [idem, Finset.sum_singleton]
  exact h

end GlobalTheory.SourceTrans

namespace GlobalTheory.SourceTrans

section LocalLift

open Formalism.MainNotions.S Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.ParahoricLift GlobalTheory.LevSplit Formalism.L2.NTheta

variable {D : D7}

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `P.isPrime` as an intermediate fact. Take `⟨p, hp, hpp, hres⟩` from `exists_idem_int he`. Take `⟨Y₀, hY₀, hdet⟩` from `exists_matrix_lift (Ideal.Quotient.mk P.asIdeal) Ideal.Quotient.mk_surjective k`. Take `⟨u, hu⟩` from `finSw_div_int he (d := Y₀.det) fun h => hdet (Ideal.Quotient.eq_zero_iff_mem.2 h)`. Take `⟨Y, hY⟩ : ∃ Y, Y = Y₀.map (oToS D.host.F D.host.E)` from `⟨_, rfl⟩`.

Establish `hu' : u * Y.det = p`. Rewrite using `[hY, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `Subtype.ext (hu.trans hp.symm)`. Establish `hmm` using `conj_inv_part β p u Y hu' hpp`. Rewrite `hmm` using `[hp]`.

Take `⟨κ, hs, hκ⟩` from `split_lift_fin V he.1 _ _ hmm`. Establish `hP : IsPrimeIdem P e (e + cA D e)` using `Or.inl ⟨he, rfl⟩`. Take `⟨-, -, T3, -⟩` from `GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V`. Establish `hsf` using `supp_fin V (f := e + cA D e) hs`. Rewrite `hκ` using `[← hp]`.

Establish `hfs : finSw D (e + cA D e) = p + Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) p`. Rewrite using `[RingHom.map_add, finSw_cA, hp]`. Establish `hSt : Lev.finE V κ ∈ St β` using `mem_St_of_part D.sp.cm.sig V.gram Λ β hf hsd p u hpp (sigR_int p.2) Y hu' (Lev.finE V κ) (finE_mem_UA V κ) _ hfs hsf hκ`. Use `⟨κ, hs, (T3 P e _ hP).2.2.1 κ hs, hSt, Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[redFn_of_smul_eq β P _ hSt p hres Y hκ, hY, ← hY₀]`.

Conclude with `Matrix.ext fun i j => resS_oToS P _`.
-/
theorem exists_local_lift' {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hf : IsFrame β Λ) (hsd : HatSelfDual D.sp.cm.sig V.gram Λ)
    {P : Pl D.host.E} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P) (k : GL (Fin V.rank) (kP P)) :
    ∃ κ : GA D V, Formalism.L2.Theta.SuppAt e V κ ∧ κ ∈ GfC V ∧ Lev.finE V κ ∈ St β ∧ redFn β P (Lev.finE V κ) = k := by
  have := P.isPrime
  obtain ⟨p, hp, hpp, hres⟩ := exists_idem_int he
  obtain ⟨Y₀, hY₀, hdet⟩ := exists_matrix_lift (Ideal.Quotient.mk P.asIdeal) Ideal.Quotient.mk_surjective k
  obtain ⟨u, hu⟩ := finSw_div_int he (d := Y₀.det) fun h => hdet (Ideal.Quotient.eq_zero_iff_mem.2 h)
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Y₀.map (oToS D.host.F D.host.E) := ⟨_, rfl⟩
  have hu' : u * Y.det = p := by
    rw [hY, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact Subtype.ext (hu.trans hp.symm)
  have hmm := conj_inv_part β p u Y hu' hpp
  rw [hp] at hmm
  obtain ⟨κ, hs, hκ⟩ := split_lift_fin V he.1 _ _ hmm
  have hP : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  have hsf := supp_fin V (f := e + cA D e) hs
  rw [← hp] at hκ
  have hfs : finSw D (e + cA D e) = p + Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) p := by
    rw [RingHom.map_add, finSw_cA, hp]
  have hSt : Lev.finE V κ ∈ St β :=
    mem_St_of_part D.sp.cm.sig V.gram Λ β hf hsd p u hpp (sigR_int p.2) Y hu' (Lev.finE V κ)
      (finE_mem_UA V κ) _ hfs hsf hκ
  refine ⟨κ, hs, (T3 P e _ hP).2.2.1 κ hs, hSt, Units.ext ?_⟩
  rw [redFn_of_smul_eq β P _ hSt p hres Y hκ, hY, ← hY₀]
  exact Matrix.ext fun i j => resS_oToS P _

end LocalLift

end GlobalTheory.SourceTrans

namespace GlobalTheory.SourceTrans

section LocalLift

open Formalism.MainNotions.S Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.ParahoricLift GlobalTheory.LevSplit Formalism.L2.NTheta

variable {D : D7}

/- English proof (translation)
Take `⟨-, -, -, -, hcc, -, -, hG, hdet, -⟩` from `GlobalTheory.Member.latHat_eq_hat_and_gram D V`. Establish `h1 : ∀ s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E` using `fun _ h => sigR_int h`. Establish `h2 : ∀ z, z ∈ GlobalTheory.AdLat.hat1 D.host.F ((1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E) ↔ swp D.host.F D.host.E z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E`. Introduce `z`. Rewrite using `[← GlobalTheory.LatDual.integralTensorAdeles_eq_adelicCompletion_one]`.

Conclude with `GlobalTheory.IdemSupport.mem_intAE_iff z`. Establish `h3 : ∀ x, D.sp.cm.sig x = GlobalTheory.Member.cF D x` using `fun _ => rfl`. Establish `hmem : ∀ v : Fin V.rank → D.host.E, (∀ y ∈ Λ, (∑ a, ∑ b, v a * V.gram.transpose a b * GlobalTheory.Member.cF D (y b)) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ↔ v ∈ Λ`. Introduce `v`. Rewrite using `[h.2 v]`.

Use `forall₂_congr fun y _ => ?_` and prove the remaining obligations. Rewrite using `[FractionalIdeal.mem_one_iff]`. Establish `e : ∑ a, ∑ b, v a * V.gram.transpose a b * GlobalTheory.Member.cF D (y b) = ∑ i, ∑ j, star (y i) * V.gram i j * v j`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.transpose_apply]`. Express the relevant statement in the definitionally equal form `v j * V.gram i j * star (y i) = _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hatL_selfDual_gen (GlobalTheory.Member.cF D) D.sp.cm.sig h3 V.gram Λ h.1.fg h.1.span_eq_top hcc hG hdet hmem h1 h2`.
-/
theorem hatSelfDual_of {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : IsSelfDualC V Λ) :
    HatSelfDual D.sp.cm.sig V.gram Λ := by
  obtain ⟨-, -, -, -, hcc, -, -, hG, hdet, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have h1 : ∀ s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun _ h => sigR_int h
  have h2 : ∀ z, z ∈ GlobalTheory.AdLat.hat1 D.host.F
      ((1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E) ↔
      swp D.host.F D.host.E z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro z
    rw [← GlobalTheory.LatDual.integralTensorAdeles_eq_adelicCompletion_one]
    exact GlobalTheory.IdemSupport.mem_intAE_iff z
  have h3 : ∀ x, D.sp.cm.sig x = GlobalTheory.Member.cF D x := fun _ => rfl
  have hmem : ∀ v : Fin V.rank → D.host.E, (∀ y ∈ Λ, (∑ a, ∑ b, v a * V.gram.transpose a b * GlobalTheory.Member.cF D (y b)) ∈
      (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ↔ v ∈ Λ := by
    intro v
    rw [h.2 v]
    refine forall₂_congr fun y _ => ?_
    rw [FractionalIdeal.mem_one_iff]
    have e : ∑ a, ∑ b, v a * V.gram.transpose a b * GlobalTheory.Member.cF D (y b) = ∑ i, ∑ j, star (y i) * V.gram i j * v j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.transpose_apply]
      change v j * V.gram i j * star (y i) = _
      ring
    rw [e]
  exact hatL_selfDual_gen (GlobalTheory.Member.cF D) D.sp.cm.sig h3 V.gram Λ h.1.fg h.1.span_eq_top hcc hG hdet hmem h1 h2

end LocalLift

variable {D : D7} {S T : HSp D} {B : Base S T}

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => exact GlobalTheory.SplitHecke.suppAt_one V`. Consider the case `cons a L ih`. Rewrite using `[List.prod_cons]`. Conclude with `GlobalTheory.SplitHecke.suppAt_mul (h a List.mem_cons_self) (ih fun g hg => h g (List.mem_cons_of_mem _ hg))`.
-/
theorem suppAt_list_prod {e : AE D} {V : HSp D} (L : List (GA D V)) (h : ∀ g ∈ L, SuppAt e V g) : SuppAt e V L.prod := by
  induction L with
  | nil => exact GlobalTheory.SplitHecke.suppAt_one V
  | cons a L ih =>
    rw [List.prod_cons]
    exact GlobalTheory.SplitHecke.suppAt_mul (h a List.mem_cons_self) (ih fun g hg => h g (List.mem_cons_of_mem _ hg))

open Classical in

/- English proof (translation)
Establish `hsQ : SplitSet Q` using `(dualTypePlaces_isSplitNonconjugate_of_admissible hQ).mono (fun PP hP => Finset.mem_union_right _ (Finset.mem_union_right _ hP))`. Establish `hsd` using `hatSelfDual_of hB.frame.sdS`. Use `choose κ h1 h2 h3 h4 using fun PP : ↥Q => exists_local_lift' hB.frame.frS hsd (hsQ.isIdemAt PP.2) (hb PP)`. Establish `hnd : (Finset.univ : Finset ↥Q).toList.Nodup` using `Finset.nodup_toList _`. Establish `hmem : ∀ PP, PP ∈ (Finset.univ : Finset ↥Q).toList` using `fun PP => Finset.mem_toList.2 (Finset.mem_univ _)`.

Establish `hSt : ∀ g ∈ (Finset.univ : Finset ↥Q).toList.map κ, Lev.finE S g ∈ St B.F.βS`. Introduce `g hg`. Take `⟨PP, -, rfl⟩` from `List.mem_map.1 hg`. Conclude with `h3 PP`. Take `⟨hS, hr⟩` from `GlobalTheory.ParahoricLift.redFn_list_prod S B.F.βS _ hSt`.

Use `⟨((Finset.univ : Finset ↥Q).toList.map κ).prod, (GfC S).list_prod_mem fun g hg => ?_, hS, suppAt_list_prod _ fun g hg => ?_, fun PP => ?_⟩` and prove the remaining obligations. Take `⟨PP, -, rfl⟩` from `List.mem_map.1 hg`. Conclude with `h2 PP`. Take `⟨PP, -, rfl⟩` from `List.mem_map.1 hg`. Conclude with `suppAt_idem_of hsQ PP.2 (h1 PP)`.

Rewrite using `[hr PP.1, List.map_map, GlobalTheory.ParahoricLift.prod_map_single hnd (hmem PP) _ fun PP' hne => ?_]`. Conclude with `h4 PP`. Conclude with `GlobalTheory.ExportSeries.redFn_eq_one_of_suppAt B.F.βS hsQ (Finset.singleton_subset_iff.2 PP'.2) PP.2 (fun h => hne (Subtype.ext (Finset.mem_singleton.1 h).symm)) (h3 PP') (suppAt_single (h1 PP'))`.
-/
theorem exists_lift_at (hB : B.Good) {Q : Finset (Pl D.host.E)} (hQ : B.admitted Q)
    (hb : ∀ PP : ↥Q, GL (Fin S.rank) (kP PP.1)) :
    ∃ k : GA D S, k ∈ GfC S ∧ Lev.finE S k ∈ St B.F.βS ∧ SuppAt (idem Q) S k ∧
      ∀ PP : ↥Q, redFn B.F.βS PP.1 (Lev.finE S k) = hb PP := by
  have hsQ : SplitSet Q := (dualTypePlaces_isSplitNonconjugate_of_admissible hQ).mono (fun PP hP => Finset.mem_union_right _ (Finset.mem_union_right _ hP))
  have hsd := hatSelfDual_of hB.frame.sdS
  choose κ h1 h2 h3 h4 using fun PP : ↥Q => exists_local_lift' hB.frame.frS hsd (hsQ.isIdemAt PP.2) (hb PP)
  have hnd : (Finset.univ : Finset ↥Q).toList.Nodup := Finset.nodup_toList _
  have hmem : ∀ PP, PP ∈ (Finset.univ : Finset ↥Q).toList := fun PP => Finset.mem_toList.2 (Finset.mem_univ _)
  have hSt : ∀ g ∈ (Finset.univ : Finset ↥Q).toList.map κ, Lev.finE S g ∈ St B.F.βS := by
    intro g hg
    obtain ⟨PP, -, rfl⟩ := List.mem_map.1 hg
    exact h3 PP
  obtain ⟨hS, hr⟩ := GlobalTheory.ParahoricLift.redFn_list_prod S B.F.βS _ hSt
  refine ⟨((Finset.univ : Finset ↥Q).toList.map κ).prod, (GfC S).list_prod_mem fun g hg => ?_, hS,
    suppAt_list_prod _ fun g hg => ?_, fun PP => ?_⟩
  · obtain ⟨PP, -, rfl⟩ := List.mem_map.1 hg
    exact h2 PP
  · obtain ⟨PP, -, rfl⟩ := List.mem_map.1 hg
    exact suppAt_idem_of hsQ PP.2 (h1 PP)
  · rw [hr PP.1, List.map_map, GlobalTheory.ParahoricLift.prod_map_single hnd (hmem PP) _ fun PP' hne => ?_]
    · exact h4 PP
    · exact GlobalTheory.ExportSeries.redFn_eq_one_of_suppAt B.F.βS hsQ (Finset.singleton_subset_iff.2 PP'.2) PP.2
        (fun h => hne (Subtype.ext (Finset.mem_singleton.1 h).symm)) (h3 PP') (suppAt_single (h1 PP'))

end GlobalTheory.SourceTrans

namespace GlobalTheory.SourceTrans

variable {D : D7} {S T : HSp D} {B : Base S T}

open Classical in
/- English proof (translation)
Establish `hν : (Twist.triv Circle Q : Twist D Circle).Good` using `Twist.triv_good ((dualTypePlaces_isSplitNonconjugate_of_admissible hQ).mono (fun PP hP => Finset.mem_union_right _ (Finset.mem_union_right _ hP)))`. Establish `hsplit` using `dualTypePlaces_isSplitNonconjugate_of_admissible hQ`. Establish `hQsub : Q ⊆ allP B Q` using `fun PP hP => Finset.mem_union_right _ (Finset.mem_union_right _ hP)`. Establish `hred1 : ∀ PP ∈ allP B Q, PP ∉ Q → redFn B.F.βS PP (Lev.finE S k) = 1` using `fun PP hP hPQ => GlobalTheory.ExportSeries.redFn_eq_one_of_suppAt B.F.βS hsplit hQsub hP hPQ sk hs`. Establish `hpg : ∀ PP ∈ B.G.Pg, PP ∉ Q` using `fun PP hP h => Finset.disjoint_left.1 hQ.1.disj hP (Finset.mem_union_right _ h)`.

Establish `hdq : ∀ PP ∈ B.de.Q, PP ∉ Q` using `fun PP hP h => Finset.disjoint_left.1 hQ.2 hP h`. Establish `hD : ∀ x, B.F.datumFn B.G (B.de.Q ∪ Q) (B.locFn Q φ) x = 1 * B.F.datumFn B.G (B.de.Q ∪ Q) (B.locFn Q (fun PP y => φ PP (y * (hb PP).val))) (actO S T k 1 x)` using `fun x => by`. Rewrite using `[datumFn_act B.F B.G (B.de.Q ∪ Q) sk (one_mem_St T _) (a := 1) (b := 1) (ω' := B.locFn Q φ) (fun y => by`. Rewrite using `[one_mul]`. Use `GlobalTheory.PlaceDatum.omegaG_congr _ _ _ _ fun PP hP => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `_ = y PP`. Simplify using `[hred1 PP (Finset.mem_union_left _ hP) (hpg PP hP), finE_one, redFn_one])`. Use the proof step `(fun y => by`. Simplify using `only [finE_one, inv_one, Units.val_one, Matrix.one_mul, one_mul]`. Unfold `Base.locFn`.

Use `congr 1`. Use `Finset.prod_congr rfl fun PP hP => ?_ dsimp only` and prove the remaining obligations. Rewrite using `[hred1 PP (Finset.mem_union_right _ (Finset.mem_union_left _ hP)) (hdq PP hP)]`. Simplify using the standard rewrite rules. Use `Finset.prod_congr rfl fun PP _ => ?_ dsimp only` and prove the remaining obligations.

Rewrite using `[hr PP, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]) x]`. Expand and normalize the polynomial expressions, which then agree. Use `(om_vec_move hB hS hν hQ hω hk (one_mem _) sk (one_mem_St T _) hD).trans ?_` and prove the remaining obligations. Establish `hv : vacC B (Twist.triv Circle Q) k 1 = 1`. Unfold `vacC`.

Use `Finset.prod_eq_one fun PP hP => ?_` and prove the remaining obligations. Rewrite using `[map_one, redFn_one, map_one, map_one, mul_one]`. Distinguish the cases in `hPQ : PP ∈ Q`. Rewrite using `[resP_q (ν := Twist.triv Circle Q) hQ hPQ]`. Simplify using `[Twist.resC, Twist.triv]`.

Rewrite using `[hred1 PP hP hPQ, map_one, map_one, inv_one]`. Rewrite using `[hv, Units.val_one, one_mul, one_smul]`. Both sides reduce to the same expression.
-/
theorem om_src_move (hB : B.Good) (hS : S.SigOK) {ω : PairRep S T} (hω : B.IsWeil 1 ω)
    {Q : Finset (Pl D.host.E)} (hQ : B.admitted Q) (hb : ∀ PP : ↥Q, GL (Fin S.rank) (kP PP.1))
    {k : GA D S} (hk : k ∈ GfC S) (sk : Lev.finE S k ∈ St B.F.βS) (hs : SuppAt (idem Q) S k)
    (hr : ∀ PP : ↥Q, redFn B.F.βS PP.1 (Lev.finE S k) = hb PP)
    (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ) :
    ω (k, 1) (B.vecAt Q φ) = B.vecAt Q (fun PP y => φ PP (y * (hb PP).val)) := by
  have hν : (Twist.triv Circle Q : Twist D Circle).Good := Twist.triv_good ((dualTypePlaces_isSplitNonconjugate_of_admissible hQ).mono
    (fun PP hP => Finset.mem_union_right _ (Finset.mem_union_right _ hP)))
  have hsplit := dualTypePlaces_isSplitNonconjugate_of_admissible hQ
  have hQsub : Q ⊆ allP B Q := fun PP hP => Finset.mem_union_right _ (Finset.mem_union_right _ hP)
  have hred1 : ∀ PP ∈ allP B Q, PP ∉ Q → redFn B.F.βS PP (Lev.finE S k) = 1 := fun PP hP hPQ =>
    GlobalTheory.ExportSeries.redFn_eq_one_of_suppAt B.F.βS hsplit hQsub hP hPQ sk hs
  have hpg : ∀ PP ∈ B.G.Pg, PP ∉ Q := fun PP hP h => Finset.disjoint_left.1 hQ.1.disj hP (Finset.mem_union_right _ h)
  have hdq : ∀ PP ∈ B.de.Q, PP ∉ Q := fun PP hP h => Finset.disjoint_left.1 hQ.2 hP h
  have hD : ∀ x, B.F.datumFn B.G (B.de.Q ∪ Q) (B.locFn Q φ) x =
      1 * B.F.datumFn B.G (B.de.Q ∪ Q) (B.locFn Q (fun PP y => φ PP (y * (hb PP).val))) (actO S T k 1 x) := fun x => by
    rw [datumFn_act B.F B.G (B.de.Q ∪ Q) sk (one_mem_St T _) (a := 1) (b := 1) (ω' := B.locFn Q φ)
      (fun y => by
        rw [one_mul]
        refine GlobalTheory.PlaceDatum.omegaG_congr _ _ _ _ fun PP hP => ?_
        change _ = y PP
        simp [hred1 PP (Finset.mem_union_left _ hP) (hpg PP hP), finE_one, redFn_one])
      (fun y => by
        simp only [finE_one, inv_one, Units.val_one, Matrix.one_mul, one_mul]
        unfold Base.locFn
        congr 1
        · refine Finset.prod_congr rfl fun PP hP => ?_
          dsimp only
          rw [hred1 PP (Finset.mem_union_right _ (Finset.mem_union_left _ hP)) (hdq PP hP)]
          simp
        · refine Finset.prod_congr rfl fun PP _ => ?_
          dsimp only
          rw [hr PP, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]) x]
    ring
  refine (om_vec_move hB hS hν hQ hω hk (one_mem _) sk (one_mem_St T _) hD).trans ?_
  have hv : vacC B (Twist.triv Circle Q) k 1 = 1 := by
    unfold vacC
    refine Finset.prod_eq_one fun PP hP => ?_
    rw [map_one, redFn_one, map_one, map_one, mul_one]
    by_cases hPQ : PP ∈ Q
    · rw [resP_q (ν := Twist.triv Circle Q) hQ hPQ]
      simp [Twist.resC, Twist.triv]
    · rw [hred1 PP hP hPQ, map_one, map_one, inv_one]
  rw [hv, Units.val_one, one_mul, one_smul]
  rfl

open Classical in
/- English proof (translation)
Establish `hth : IsThetaFunO B.F.ψ S T (B.vecAt Q φ)` using `GlobalTheory.GalLift.Vec.theta_of_thetaAt hB.frame.vac.1 hB.frame.vac.2.inf (Base.isThetaAt_vecAt hB hQ φ) hB.frame.vac.2.theta`. Rewrite using `[Frame.fock, (GlobalTheory.OrientedHeis.om_pureTensorO D _ _ S T _ _ ω hω hB.frame.vac.2.inf (fun _ => 1) (fun _ => 1) (fun τ => (B.F.BS τ).val) (fun τ => (B.F.BS τ).val) B.F.sT B.F.sT B.F.BT B.F.BT k 1 (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hk]) (fun …`. Both sides reduce to the same expression.
-/
theorem om_src_fock (hB : B.Good) (hS : S.SigOK) {ω : PairRep S T} (hω : B.IsWeil 1 ω)
    {Q : Finset (Pl D.host.E)} (hQ : B.admitted Q) (hb : ∀ PP : ↥Q, GL (Fin S.rank) (kP PP.1))
    {k : GA D S} (hk : k ∈ GfC S) (sk : Lev.finE S k ∈ St B.F.βS) (hs : SuppAt (idem Q) S k)
    (hr : ∀ PP : ↥Q, redFn B.F.βS PP.1 (Lev.finE S k) = hb PP)
    (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ) (P : PolF D T.rank S.rank) :
    ω (k, 1) (B.F.fock (B.vecAt Q φ) P) = B.F.fock (B.vecAt Q (fun PP y => φ PP (y * (hb PP).val))) P := by
  have hth : IsThetaFunO B.F.ψ S T (B.vecAt Q φ) :=
    GlobalTheory.GalLift.Vec.theta_of_thetaAt hB.frame.vac.1 hB.frame.vac.2.inf (Base.isThetaAt_vecAt hB hQ φ) hB.frame.vac.2.theta
  rw [Frame.fock, (GlobalTheory.OrientedHeis.om_pureTensorO D _ _ S T _ _ ω hω hB.frame.vac.2.inf (fun _ => 1) (fun _ => 1)
      (fun τ => (B.F.BS τ).val) (fun τ => (B.F.BS τ).val) B.F.sT B.F.sT B.F.BT B.F.BT k 1
      (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hk])
      (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _)])
      (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hk])
      (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _)]) _ hth P).2,
    om_src_move hB hS hω hQ hb hk sk hs hr φ]
  rfl

end GlobalTheory.SourceTrans

open GlobalTheory.SourceTrans in
/- English proof (translation)
Introduce `D S T B hB hS ω hω Q hQ hb`. Take `⟨k, hk, sk, hs, hr⟩` from `exists_lift_at hB hQ hb`. Use `⟨k, hs, fun φ h P => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Rewrite using `[series_apply, series_apply, show ((h * k, g) : GA D S × GA D T) = (h, g) * (k, 1) by simp, map_mul, Module.End.mul_apply, om_src_fock hB hS hω hQ hb hk sk hs hr φ P]`.
-/
theorem GlobalTheory.SourceTrans.exists_series_vecAt_translate_eq_series_mul : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ ω : PairRep S T, B.IsWeil 1 ω → ∀ (Q : Finset (Pl D.host.E)), B.admitted Q → ∀ hb : ∀ PP : ↥Q, GL (Fin S.rank) (kP PP.1), ∃ hQ, SuppAt (idem Q) S hQ ∧ ∀ (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ) (h : GA D S) (P : PolF D T.rank S.rank), series B.F ω (B.vecAt Q fun PP y => φ PP (y * (hb PP).val)) h P = series B.F ω (B.vecAt Q φ) (h * hQ) P := by
  intro D S T B hB hS ω hω Q hQ hb
  obtain ⟨k, hk, sk, hs, hr⟩ := exists_lift_at hB hQ hb
  refine ⟨k, hs, fun φ h P => ?_⟩
  funext g
  rw [series_apply, series_apply, show ((h * k, g) : GA D S × GA D T) = (h, g) * (k, 1) by simp, map_mul,
    Module.End.mul_apply, om_src_fock hB hS hω hQ hb hk sk hs hr φ P]
