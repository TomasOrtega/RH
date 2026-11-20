import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.TorusScalar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsJLeviMulJPlus
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IwahoriNeBotOfSpherical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.Gal.TypesAndIwahori

/- English proof (translation)
Introduce `L k _ _ _ _ N s d e V _ _ π hs hi θ μ hμ ⟨v, hv0, hv⟩`. Establish `hadm : IsAdmissible π` using `(L.bz k).1 (Fin N) V π hs hi`. Establish `hb` using `L.mp k N s d e V π hadm`. Establish `hJ : KOne k (Fin N) ⊔ (unipRad k e ⊓ KO k (Fin N)) = proRad k e` using `(GlobalTheory.LocGL.IwahoriFactor.proRad_eq_sup e).symm`. Rewrite `hb` using `[hJ]`.

Establish `key : ∀ g ∈ proRad k e, π g v = v`. Introduce `g hg`. Establish `hp : g ∈ parahoric k e` using `proRad_le_parahoric e hg`. Establish `h1 : parahoricProj k e ⟨g, hp⟩ = 1` using `(parahoricProj_eq_one_iff e ⟨g, hp⟩).2 hg`. Establish `h2 : π g v = ((typeChar e θ ⟨g, hp⟩ : ℂˣ) : ℂ) • v` using `hv ⟨g, hp⟩`.

Establish `h3 : typeChar e θ ⟨g, hp⟩ = 1` using `by show leviChar _ θ (parahoricProj k e ⟨g, hp⟩) = 1`. Rewrite using `[h1, map_one]`. Rewrite using `[h2, h3, Units.val_one, one_smul]`. Establish `hfix : v ∈ fixed π (proRad k e)` using `GlobalTheory.Cong.LimitAtL.mem_fixed.2 key`. Establish `h0 : (0 : V) ∈ fixed π (proRad k e)` using `zero_mem _`.

Use `⟨Submodule.Quotient.mk v, fun hy => hv0 (hb.injOn hfix h0 ?_), fun x hx => ?_⟩` and prove the remaining obligations. Simplify using `using hy`. Establish `h1 : jacU e π x (Submodule.Quotient.mk v) = Submodule.Quotient.mk (π (leviEmb k e x) v)` using `rfl`. Establish `h2` using `hv ⟨leviEmb k e x, leviEmb_mem_parahoric e ⟨x, hx⟩⟩`. Establish `h3 : π (leviEmb k e x) v = ((typeChar e θ ⟨leviEmb k e x, leviEmb_mem_parahoric e ⟨x, hx⟩⟩ : ℂˣ) : ℂ) • v` using `h2`.

Establish `h4 : ∀ a, ((μ a (GeneralLinearGroup.det (x a)) : ℂˣ) : ℂ) = ((θ a (GeneralLinearGroup.det (redLevi k _ ⟨x, hx⟩ a)) : ℂˣ) : ℂ)`. Introduce `a`. Establish `h5` using `(hμ a).detChar_eq ⟨x a, hx a trivial⟩`. Rewrite using `[redLevi_apply]`. Conclude with `congrArg (fun u : ℂˣ => (u : ℂ)) h5`.

Establish `h6 : parahoricProj k e ⟨leviEmb k e x, leviEmb_mem_parahoric e ⟨x, hx⟩⟩ = redLevi k _ ⟨x, hx⟩` using `parahoricProj_leviEmb e ⟨x, hx⟩`. Rewrite using `[h1, h3, typeChar_apply, h6, Units.coe_prod, Submodule.Quotient.mk_smul]`. Simplify using `only [h4]`.
-/
theorem UpperTheory.Gal.TypesAndIwahori.jacOfType :
    UpperTheory.Gal.TypesAndIwahori.Loc → UpperTheory.Gal.TypesAndIwahori.JacOfType := by
  intro L k _ _ _ _ N s d e V _ _ π hs hi θ μ hμ ⟨v, hv0, hv⟩
  have hadm : IsAdmissible π := (L.bz k).1 (Fin N) V π hs hi
  have hb := L.mp k N s d e V π hadm
  have hJ : KOne k (Fin N) ⊔ (unipRad k e ⊓ KO k (Fin N)) = proRad k e :=
    (GlobalTheory.LocGL.IwahoriFactor.proRad_eq_sup e).symm
  rw [hJ] at hb
  have key : ∀ g ∈ proRad k e, π g v = v := by
    intro g hg
    have hp : g ∈ parahoric k e := proRad_le_parahoric e hg
    have h1 : parahoricProj k e ⟨g, hp⟩ = 1 := (parahoricProj_eq_one_iff e ⟨g, hp⟩).2 hg
    have h2 : π g v = ((typeChar e θ ⟨g, hp⟩ : ℂˣ) : ℂ) • v := hv ⟨g, hp⟩
    have h3 : typeChar e θ ⟨g, hp⟩ = 1 := by
      show leviChar _ θ (parahoricProj k e ⟨g, hp⟩) = 1
      rw [h1, map_one]
    rw [h2, h3, Units.val_one, one_smul]
  have hfix : v ∈ fixed π (proRad k e) := GlobalTheory.Cong.LimitAtL.mem_fixed.2 key
  have h0 : (0 : V) ∈ fixed π (proRad k e) := zero_mem _
  refine ⟨Submodule.Quotient.mk v, fun hy => hv0 (hb.injOn hfix h0 ?_), fun x hx => ?_⟩
  · simpa using hy
  · have h1 : jacU e π x (Submodule.Quotient.mk v) = Submodule.Quotient.mk (π (leviEmb k e x) v) := rfl
    have h2 := hv ⟨leviEmb k e x, leviEmb_mem_parahoric e ⟨x, hx⟩⟩
    have h3 : π (leviEmb k e x) v = ((typeChar e θ ⟨leviEmb k e x, leviEmb_mem_parahoric e ⟨x, hx⟩⟩ : ℂˣ) : ℂ) • v := h2
    have h4 : ∀ a, ((μ a (GeneralLinearGroup.det (x a)) : ℂˣ) : ℂ) =
        ((θ a (GeneralLinearGroup.det (redLevi k _ ⟨x, hx⟩ a)) : ℂˣ) : ℂ) := by
      intro a
      have h5 := (hμ a).detChar_eq ⟨x a, hx a trivial⟩
      rw [redLevi_apply]
      exact congrArg (fun u : ℂˣ => (u : ℂ)) h5
    have h6 : parahoricProj k e ⟨leviEmb k e x, leviEmb_mem_parahoric e ⟨x, hx⟩⟩ = redLevi k _ ⟨x, hx⟩ :=
      parahoricProj_leviEmb e ⟨x, hx⟩
    rw [h1, h3, typeChar_apply, h6, Units.coe_prod, Submodule.Quotient.mk_smul]
    simp only [h4]
