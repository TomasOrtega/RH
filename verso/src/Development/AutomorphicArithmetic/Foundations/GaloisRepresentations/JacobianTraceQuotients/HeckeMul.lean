import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuot

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

/- English proof (translation)
Rewrite using `[map_mul, Module.End.mul_apply]`.
-/
private theorem rep_mul {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    (a b : G) (w : V) : π (a * b) w = π a (π b w) := by
  rw [map_mul, Module.End.mul_apply]

/- English proof (translation)
Take `⟨u, hu, d, hd, c, hc, rfl⟩` from `hK.fact g hg`. Use `⟨u, hu, ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ x : K, π x v = ((1 : K →* ℂˣ) x : ℂ) • v` using `hv`. Establish `hfix : ∀ h ∈ K, π h v = v` using `fun h hh => by simpa using h1 ⟨h, hh⟩`. Establish `hc'` using `hK.low t ht c hc`.

Establish `hcomm : diagT k (Fin n) d * diagT k (Fin n) t = diagT k (Fin n) t * diagT k (Fin n) d`. Rewrite using `[← map_mul, ← map_mul, mul_comm]`. Establish `key : u * diagT k (Fin n) d * c * diagT k (Fin n) t = u * diagT k (Fin n) t * (diagT k (Fin n) d * ((diagT k (Fin n) t)⁻¹ * c * diagT k (Fin n) t))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← rep_mul π (u * diagT k (Fin n) d * c), key, rep_mul π (u * diagT k (Fin n) t), rep_mul π (diagT k (Fin n) d), hfix _ hc', hfix _ hd, rep_mul]`.
-/
private theorem exists_unipotent_eq_of_mem_iwLev_of_fixed {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] {n : ℕ}
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (K : Subgroup (GL (Fin n) k)) (hK : IwLev K) (t : Fin n → kˣ) (ht : Dom t) (v : V)
    (hv : v ∈ fixed π K) (g : GL (Fin n) k) (hg : g ∈ K) :
    ∃ u ∈ K ⊓ unipB k (Fin n),
      π g (π (diagT k (Fin n) t) v) = π u (π (diagT k (Fin n) t) v) := by
  obtain ⟨u, hu, d, hd, c, hc, rfl⟩ := hK.fact g hg
  refine ⟨u, hu, ?_⟩
  have h1 : ∀ x : K, π x v = ((1 : K →* ℂˣ) x : ℂ) • v := hv
  have hfix : ∀ h ∈ K, π h v = v := fun h hh => by simpa using h1 ⟨h, hh⟩
  have hc' := hK.low t ht c hc
  have hcomm : diagT k (Fin n) d * diagT k (Fin n) t = diagT k (Fin n) t * diagT k (Fin n) d := by
    rw [← map_mul, ← map_mul, mul_comm]
  have key : u * diagT k (Fin n) d * c * diagT k (Fin n) t =
      u * diagT k (Fin n) t * (diagT k (Fin n) d *
        ((diagT k (Fin n) t)⁻¹ * c * diagT k (Fin n) t)) := by
    calc u * diagT k (Fin n) d * c * diagT k (Fin n) t
        = u * (diagT k (Fin n) d * diagT k (Fin n) t) *
            ((diagT k (Fin n) t)⁻¹ * c * diagT k (Fin n) t) := by group
      _ = u * (diagT k (Fin n) t * diagT k (Fin n) d) *
            ((diagT k (Fin n) t)⁻¹ * c * diagT k (Fin n) t) := by rw [hcomm]
      _ = _ := by group
  rw [← rep_mul π (u * diagT k (Fin n) d * c), key, rep_mul π (u * diagT k (Fin n) t),
    rep_mul π (diagT k (Fin n) d), hfix _ hc', hfix _ hd, rep_mul]

/- English proof (translation)
Unfold `UpperTheory.Gal.Join.HeckeMul UpperTheory.Gal.Join.ForRep`. Introduce `k _ _ _ _ n V _ _ π K hK e he t ht v hv`. Establish `hN : ∀ u ∈ K ⊓ unipB k (Fin n), ∀ w : V, (twKer π (unipB k (Fin n)) 1).mkQ (π u w) = (twKer π (unipB k (Fin n)) 1).mkQ w`. Introduce `u hu w`. Rewrite using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]`.

Conclude with `Submodule.subset_span ⟨⟨u, (Subgroup.mem_inf.mp hu).2⟩, w, by simp⟩`. Use `⟨fun s hs => ?_, ?_⟩` and prove the remaining obligations. Establish `h2` using `he.lin V (e.comp (π (diagT k (Fin n) s))) (π (diagT k (Fin n) t) v) ?_`. Simplify using `only [LinearMap.comp_apply] at h2`. Rewrite using `[h2, map_mul, rep_mul]`.

Introduce `g hg`. Take `⟨u, hu, hgu⟩` from `exists_unipotent_eq_of_mem_iwLev_of_fixed π K hK t ht v hv g hg`. Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[hgu, ← rep_mul π (diagT k (Fin n) s) u, show diagT k (Fin n) s * u = (diagT k (Fin n) s * u * (diagT k (Fin n) s)⁻¹) * diagT k (Fin n) s by group, rep_mul π (diagT k (Fin n) s * u * (diagT k (Fin n) s)⁻¹), he.inv _ (hK.up s hs u hu)]`. Establish `h3` using `he.lin _ (twKer π (unipB k (Fin n)) 1).mkQ (π (diagT k (Fin n) t) v) ?_`.

Conclude with `h3.trans rfl`. Introduce `g hg`. Take `⟨u, hu, hgu⟩` from `exists_unipotent_eq_of_mem_iwLev_of_fixed π K hK t ht v hv g hg`. Rewrite using `[hgu, hN u hu]`.
-/
theorem UpperTheory.Gal.Join.heckeMul :
    UpperTheory.Gal.Join.HeckeMul := by
  unfold UpperTheory.Gal.Join.HeckeMul UpperTheory.Gal.Join.ForRep
  intro k _ _ _ _ n V _ _ π K hK e he t ht v hv
  have hN : ∀ u ∈ K ⊓ unipB k (Fin n), ∀ w : V,
      (twKer π (unipB k (Fin n)) 1).mkQ (π u w) = (twKer π (unipB k (Fin n)) 1).mkQ w := by
    intro u hu w
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact Submodule.subset_span ⟨⟨u, (Subgroup.mem_inf.mp hu).2⟩, w, by simp⟩
  refine ⟨fun s hs => ?_, ?_⟩
  · have h2 := he.lin V (e.comp (π (diagT k (Fin n) s))) (π (diagT k (Fin n) t) v) ?_
    · simp only [LinearMap.comp_apply] at h2
      rw [h2, map_mul, rep_mul]
    · intro g hg
      obtain ⟨u, hu, hgu⟩ := exists_unipotent_eq_of_mem_iwLev_of_fixed π K hK t ht v hv g hg
      simp only [LinearMap.comp_apply]
      rw [hgu, ← rep_mul π (diagT k (Fin n) s) u,
        show diagT k (Fin n) s * u =
          (diagT k (Fin n) s * u * (diagT k (Fin n) s)⁻¹) * diagT k (Fin n) s by group,
        rep_mul π (diagT k (Fin n) s * u * (diagT k (Fin n) s)⁻¹),
        he.inv _ (hK.up s hs u hu)]
  · have h3 := he.lin _ (twKer π (unipB k (Fin n)) 1).mkQ (π (diagT k (Fin n) t) v) ?_
    · exact h3.trans rfl
    · intro g hg
      obtain ⟨u, hu, hgu⟩ := exists_unipotent_eq_of_mem_iwLev_of_fixed π K hK t ht v hv g hg
      rw [hgu, hN u hu]
