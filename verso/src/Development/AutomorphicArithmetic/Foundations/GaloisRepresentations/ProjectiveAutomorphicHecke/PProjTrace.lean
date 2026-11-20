import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap

open Module
universe u v

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.CertificateRingHomMap.pProjTrace_holds :
    UpperTheory.Gal.CertificateRingHomMap.ProjTrace.{u} := by
  intro F _ W _ _ _ U p u hp h
  set q : W →ₗ[F] U := LinearMap.codRestrict U p hp.map_mem with hq
  have h1 : u * p = U.subtype ∘ₗ ((LinearMap.restrict u h) ∘ₗ q) := by
    ext x
    simp [q, LinearMap.restrict_apply]
  have h2 : q ∘ₗ U.subtype = LinearMap.id := by
    ext x
    simp [q, hp.map_id x x.2]
  rw [h1, LinearMap.trace_comp_comm', LinearMap.comp_assoc, h2, LinearMap.comp_id]
