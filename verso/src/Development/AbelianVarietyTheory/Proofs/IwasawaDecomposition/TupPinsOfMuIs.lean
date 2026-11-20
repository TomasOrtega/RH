import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PointPropertyEqSizeFree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTwistOfIsDelta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.HD.TupPin

/- English proof (translation)
Establish `a1 : Chr.IsTwist B.host (Set.range B.host.g) f.del` using `Chr.isTwist_of_isDelta B.host.pde_prime (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ B.host.pde_prime B.pde_cond.1).1 (fun ⟨i, h⟩ => (B.host.pde_ne_g i).1 h.symm) f.isDel`. Establish `a2 : Chr.IsTwist B.host (Set.range B.host.g) f.del'` using `Chr.isTwist_of_isDelta B.host.pde'_prime (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ B.host.pde'_prime B.pde_cond.2).1 (fun ⟨i, h⟩ => (B.host.pde_ne_g i).2 h.symm) f.isDel'`. Introduce and unpack `ξ ((rfl | rfl | rfl) | ⟨w, rfl⟩)`. Conclude with `Chr.isTwist_one _ _`. Conclude with `a1`.

Conclude with `a2`. Establish `h` using `T.psi_tw w`. Establish `a3 : Chr.IsTwist B.host (Set.range B.host.g) (T.psi w)` using `⟨h.1, h.2.1, h.2.2.1, fun v hv => ⟨(h.2.2.2 v hv).1, (h.2.2.2 v hv).2.1, (h.2.2.2 v hv).2.2.1, fun ⟨i, hi⟩ => (h.2.2.2 v hv).2.2.2 (Or.inr (Or.inl ⟨i, hi.symm⟩))⟩⟩`. Unfold `TwDat.xiTw`. Use `split_ifs`.

Use `exacts [a2.mul_twist a3, a1.mul_twist a3]`.
-/
theorem isTwist_types (B : Base) (f : Fr B.toPre) (T : TwDat B) :
    ∀ ξ ∈ T.set f, Chr.IsTwist B.host (Set.range B.host.g) ξ := by
  have a1 : Chr.IsTwist B.host (Set.range B.host.g) f.del := Chr.isTwist_of_isDelta B.host.pde_prime
    (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ B.host.pde_prime B.pde_cond.1).1
    (fun ⟨i, h⟩ => (B.host.pde_ne_g i).1 h.symm) f.isDel
  have a2 : Chr.IsTwist B.host (Set.range B.host.g) f.del' := Chr.isTwist_of_isDelta B.host.pde'_prime
    (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ B.host.pde'_prime B.pde_cond.2).1
    (fun ⟨i, h⟩ => (B.host.pde_ne_g i).2 h.symm) f.isDel'
  rintro ξ ((rfl | rfl | rfl) | ⟨w, rfl⟩)
  · exact Chr.isTwist_one _ _
  · exact a1
  · exact a2
  · have h := T.psi_tw w
    have a3 : Chr.IsTwist B.host (Set.range B.host.g) (T.psi w) := ⟨h.1, h.2.1, h.2.2.1, fun v hv =>
      ⟨(h.2.2.2 v hv).1, (h.2.2.2 v hv).2.1, (h.2.2.2 v hv).2.2.1,
        fun ⟨i, hi⟩ => (h.2.2.2 v hv).2.2.2 (Or.inr (Or.inl ⟨i, hi.symm⟩))⟩⟩
    unfold TwDat.xiTw
    split_ifs
    exacts [a2.mul_twist a3, a1.mul_twist a3]

/- English proof (translation)
Establish `hψ : (T.psi w).UnrAt v` using `fun x _ => (T.psi_is w).atl v hv x`. Unfold `TwDat.xiTw`. Use `split_ifs with h`. Use `(f.isDel'.unr v fun hn => B.host.pde_ne ?_).mul hψ` and prove the remaining obligations. Rewrite `hv` using `[h]`.

Conclude with `Examples₂.PlacesToy.prime_mem_unique v B.host.pde_prime B.host.pde'_prime hv hn`. Conclude with `(f.isDel.unr v fun hn => h (Examples₂.PlacesToy.prime_mem_unique v (B.places.resChar_prime w) B.host.pde_prime hv hn)).mul hψ`.
-/
theorem xiTw_unr (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : B.places.Pl) (v : HeightOneSpectrum (𝓞 B.host.E))
    (hv : OverP B.host (B.places.resChar w) v) : (T.xiTw f w).UnrAt v := by
  have hψ : (T.psi w).UnrAt v := fun x _ => (T.psi_is w).atl v hv x
  unfold TwDat.xiTw
  split_ifs with h
  · refine (f.isDel'.unr v fun hn => B.host.pde_ne ?_).mul hψ
    rw [h] at hv
    exact Examples₂.PlacesToy.prime_mem_unique v B.host.pde_prime B.host.pde'_prime hv hn
  · exact (f.isDel.unr v fun hn => h
      (Examples₂.PlacesToy.prime_mem_unique v (B.places.resChar_prime w) B.host.pde_prime hv hn)).mul hψ

/- English proof (translation)
Introduce `X f T xi h nch tp hxi`. Use `⟨fun μ v hv => ?_, fun w v hv => ?_⟩` and prove the remaining obligations. Rewrite `hv` using `[hxi]`. Take `⟨h1, h2, h3, h4⟩` from `(isTwist_types X.B f T (xi μ) (h.range ▸ Set.mem_range_self μ)).2.2.2 v hv`. Conclude with `⟨h1, h2, h3, fun k hk => h4 ⟨k, Examples₂.PlacesToy.prime_mem_unique v (X.B.host.g_prime k) h2 hk (Ideal.absNorm_mem _)⟩⟩`.

Rewrite using `[hxi] show (xi (X.W.muAt w)).UnrAt v`. Distinguish the cases in `hw : X.B.places.resChar w ∈ T.pl`. Rewrite using `[h.on w hw, h.tw w]`. Conclude with `xiTw_unr X.B f T w v hv`. Rewrite using `[h.off w hw, h.mu0]`.

Conclude with `fun x _ => HChar.loc_one _ _`.
-/
theorem tupPins_of_muIs : ∀ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (xi : X.C.Tup → HChar X.B.host.E), MuIs X f T xi → ∀ (nch : NChoice X.toD7) (tp : TupTied X.toD7 (Fr.at X f) nch), tp.xi = xi → TupPins tp := by
  intro X f T xi h nch tp hxi
  refine ⟨fun μ v hv => ?_, fun w v hv => ?_⟩
  · rw [hxi] at hv
    obtain ⟨h1, h2, h3, h4⟩ := (isTwist_types X.B f T (xi μ) (h.range ▸ Set.mem_range_self μ)).2.2.2 v hv
    exact ⟨h1, h2, h3, fun k hk => h4
      ⟨k, Examples₂.PlacesToy.prime_mem_unique v (X.B.host.g_prime k) h2 hk (Ideal.absNorm_mem _)⟩⟩
  · rw [hxi]
    show (xi (X.W.muAt w)).UnrAt v
    by_cases hw : X.B.places.resChar w ∈ T.pl
    · rw [h.on w hw, h.tw w]
      exact xiTw_unr X.B f T w v hv
    · rw [h.off w hw, h.mu0]
      exact fun x _ => HChar.loc_one _ _

end GlobalTheory.Mem.HD.TupPin
