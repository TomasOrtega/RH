import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LiftRows.Inh
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

/- English proof (translation)
Introduce `k`. Establish `: Fact (D.host.g k).Prime` using `⟨D.host.g_prime k⟩`. Use `⟨_, (h.teich k).symm, h.ser k, fun v j PP hPP a u ha hu => Or.inl ?_⟩` and prove the remaining obligations. Establish `hl` using `h.isCharLab k v j`. Establish `hp` using `D.host.g_prime k`.

Establish `ha0 : (a : Formalism.CyclotomicNorms.Fbar (D.host.g k)) ≠ 0`. Rewrite using `[ha]`. Introduce `h0`. Use `(GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen_order 1 one_pos` as an intermediate fact. Rewrite `this` using `[h0, pow_one]`.

Establish `h2` using `hp.two_le`. Establish `h3 : orderOf (0 : Formalism.CyclotomicNorms.Fbar (D.host.g k)) = 0` using `orderOf_eq_zero_iff'.2 fun n hn => by simp [hn.ne']`. Use linear arithmetic over natural numbers and integers. Establish `hcop : a.Coprime (D.host.g k)`. Rewrite using `[Nat.coprime_comm, hp.coprime_iff_not_dvd]`.

Introduce `hd`. Conclude with `ha0 ((CharP.cast_eq_zero_iff _ (D.host.g k) a).2 hd)`. Establish `han : a ≠ 0` using `by rintro rfl; exact ha0 (by simp)`. Establish `h1` using `hl.2 (ZMod.unitOfCoprime a hcop) (by rw [ZMod.coe_unitOfCoprime, map_natCast, ha])`. Rewrite using `[← h1]`.

Establish `hE : (a : D.host.E) ≠ 0` using `by exact_mod_cast han`. Establish `h2` using `(R.C.isMu0 j).atg k PP hPP a hcop (Units.mk0 _ hE) rfl`. Establish `h3` using `hL.chi j PP ((hL.Pg PP).2 ⟨k, hPP⟩) (a : 𝓞 D.host.E) (Units.mk0 _ hE) u (by simp) (by rw [hu, map_natCast])`. Rewrite `h3` using `[h2, MonoidHom.inv_apply, _root_.inv_inj]`. Rewrite using `[h3, MonoidHom.pow_apply]`.
-/
theorem goodTypes_of_typesTrue (hL : R.toLevCh.Is A.μ0) (h : GlobalTheory.Mem.Top.TypesTrue D.ntypes R.C.P R.C.W) :
    GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R := by
  intro k
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  refine ⟨_, (h.teich k).symm, h.ser k, fun v j PP hPP a u ha hu => Or.inl ?_⟩
  have hl := h.isCharLab k v j
  have hp := D.host.g_prime k
  have ha0 : (a : Formalism.CyclotomicNorms.Fbar (D.host.g k)) ≠ 0 := by
    rw [ha]; intro h0
    have := (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen_order 1 one_pos
    rw [h0, pow_one] at this
    have h2 := hp.two_le
    have h3 : orderOf (0 : Formalism.CyclotomicNorms.Fbar (D.host.g k)) = 0 := orderOf_eq_zero_iff'.2 fun n hn => by simp [hn.ne']
    omega
  have hcop : a.Coprime (D.host.g k) := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hd
    exact ha0 ((CharP.cast_eq_zero_iff _ (D.host.g k) a).2 hd)
  have han : a ≠ 0 := by rintro rfl; exact ha0 (by simp)
  have h1 := hl.2 (ZMod.unitOfCoprime a hcop) (by rw [ZMod.coe_unitOfCoprime, map_natCast, ha])
  rw [← h1]
  have hE : (a : D.host.E) ≠ 0 := by exact_mod_cast han
  have h2 := (R.C.isMu0 j).atg k PP hPP a hcop (Units.mk0 _ hE) rfl
  have h3 := hL.chi j PP ((hL.Pg PP).2 ⟨k, hPP⟩) (a : 𝓞 D.host.E) (Units.mk0 _ hE) u (by simp) (by rw [hu, map_natCast])
  rw [h2, MonoidHom.inv_apply, _root_.inv_inj] at h3
  rw [h3, MonoidHom.pow_apply]

end GlobalTheory.LiftRows.Inh
end
