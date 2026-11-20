import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittModuleLengthCompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueKernelOrderPPowerDegreeIsogenyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasKernelOrderPPowerDegreeCompLeAddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupIsogenyBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelDegreeLeDieudonneColengthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenousPDivGroupFinrankOmegaDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFunctorBaseFunctorPropertiesStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

/- English proof (translation)
Introduce `p _ T k _ _ _ G H q e hq he`. Take `⟨n, g, hqg, hgq⟩` from `hq`. Establish `hq' : IsIsog q` using `⟨n, g, hqg, hgq⟩`. Establish `hg : IsIsog g` using `⟨n, q, hgq, hqg⟩`. Take `⟨e', he', -⟩` from `GlobalTheory.T.existsUnique_kernelOrder_pPowerDegree_isogeny p k H G g hg`.

Establish `hpG` using `((GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k G).1 n).2`. Rewrite `hpG` using `[← hqg]`. Establish `hle : n * G.height ≤ e + e'` using `GlobalTheory.T.hasKernelOrderPPowerDegree_comp_le_add p k G H G q g e e' _ he he' hpG`. Establish `h1` using `GlobalTheory.T.kernelDegree_le_dieudonneColength p T k G H q e hq' he`. Establish `h2` using `GlobalTheory.T.kernelDegree_le_dieudonneColength p T k H G g e' hg he'`.

Take `⟨hinj, hfin1, -⟩` from `GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G H q hq'`. Take `⟨-, hfin2, -⟩` from `GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k H G g hg`. Take `⟨hid, hcomp, -, -, -, -, -, hrank, -⟩` from `GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G H G trivial trivial trivial`. Take `⟨-, -, -, -, hsmulG, -⟩` from `GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G G G trivial trivial trivial`. Take `⟨hadd, hpow, -⟩` from `GlobalTheory.T.witt_module_length_composition p k (T.M G) (T.M H) (T.M G)`.

Establish `hsum` using `hadd (T.map q) (T.map g) hinj`. Establish `hcomp' : T.map q ∘ₗ T.map g = T.map (q ≫ g)` using `(hcomp q g).symm`. Establish `hmul : ∀ a : T.M G, (T.map q ∘ₗ T.map g) a = p ^ n • a`. Introduce `a`. Rewrite using `[hcomp', hqg]`.

Use `show T.base.map trivial trivial ((p : ℤ_[p]) ^ n • 𝟙 G) a = p ^ n • a`. Rewrite using `[hsmulG n (𝟙 G) a, hid]`. Both sides reduce to the same expression. Establish `hn` using `hpow (T.base.free G trivial) (T.base.finite G trivial) n _ hmul`. Rewrite `hsum` using `[hn, hrank]`.

Take `⟨a, ha⟩` from `ENat.ne_top_iff_exists.mp hfin1`. Take `⟨b, hb⟩` from `ENat.ne_top_iff_exists.mp hfin2`. Rewrite `h1`, `hsum`, the goal using `[← ha]`. Rewrite `h2`, `hsum` using `[← hb]`. Normalize the coercions in `at h1 h2 hsum ⊢`.

Use linear arithmetic over natural numbers and integers.
-/
theorem length_quot_range_map_eq_of_hasLogDeg : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (e : ℕ), IsIsog q → HasLogDeg q e →
    Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) = e := by
  intro p _ T k _ _ _ G H q e hq he
  obtain ⟨n, g, hqg, hgq⟩ := hq
  have hq' : IsIsog q := ⟨n, g, hqg, hgq⟩
  have hg : IsIsog g := ⟨n, q, hgq, hqg⟩
  obtain ⟨e', he', -⟩ := GlobalTheory.T.existsUnique_kernelOrder_pPowerDegree_isogeny p k H G g hg
  have hpG := ((GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k G).1 n).2
  rw [← hqg] at hpG
  have hle : n * G.height ≤ e + e' := GlobalTheory.T.hasKernelOrderPPowerDegree_comp_le_add p k G H G q g e e' _ he he' hpG
  have h1 := GlobalTheory.T.kernelDegree_le_dieudonneColength p T k G H q e hq' he
  have h2 := GlobalTheory.T.kernelDegree_le_dieudonneColength p T k H G g e' hg he'
  obtain ⟨hinj, hfin1, -⟩ := GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G H q hq'
  obtain ⟨-, hfin2, -⟩ := GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k H G g hg
  obtain ⟨hid, hcomp, -, -, -, -, -, hrank, -⟩ :=
    GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G H G trivial trivial trivial
  obtain ⟨-, -, -, -, hsmulG, -⟩ :=
    GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
  obtain ⟨hadd, hpow, -⟩ := GlobalTheory.T.witt_module_length_composition p k (T.M G) (T.M H) (T.M G)
  have hsum := hadd (T.map q) (T.map g) hinj
  have hcomp' : T.map q ∘ₗ T.map g = T.map (q ≫ g) := (hcomp q g).symm
  have hmul : ∀ a : T.M G, (T.map q ∘ₗ T.map g) a = p ^ n • a := by
    intro a
    rw [hcomp', hqg]
    show T.base.map trivial trivial ((p : ℤ_[p]) ^ n • 𝟙 G) a = p ^ n • a
    rw [hsmulG n (𝟙 G) a, hid]
    rfl
  have hn := hpow (T.base.free G trivial) (T.base.finite G trivial) n _ hmul
  rw [hn, hrank] at hsum
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hfin1
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hfin2
  rw [← ha] at h1 hsum ⊢
  rw [← hb] at h2 hsum
  norm_cast at h1 h2 hsum ⊢
  omega

end GlobalTheory.Dieu
