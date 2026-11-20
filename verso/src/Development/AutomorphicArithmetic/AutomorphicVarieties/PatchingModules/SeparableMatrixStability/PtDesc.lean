import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PtUnip
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.NpDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.BDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.ComapLam

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
Introduce `l _ L G0 T Q n O _ _ _ r r' B _ _ _ u u' D0 P hA hC hD hψ`. Establish `hU` using `UpperTheory.V.Pa.pt_unip l L G0 T n O r B u D0 P hA`. Take `⟨⟨ρ', hρ⟩, κ', hκ⟩` from `UpperTheory.V.Pa.np_desc l L G0 Q.G0' Q.g0 n P.x P.k (T.H.toOpenSubgroup : Subgroup G0.Γ) T.H.toOpenSubgroup.isOpen' (fun g hg => MonoidHom.mem_ker.2 (T.H_η g hg)) hU Q.ker0`. Establish `hb` using `UpperTheory.V.Pa.b_desc l L G0 T Q n P.x P.k ρ' hρ κ' hκ D0 hU`. Use `letI := P.alg`.

Establish `hmat : (mat ρ').comp Q.g0.p₀ = mat P.x.ρ`. Use extensionality with `a i j`. Simplify using `[mat, hρ]`. Use `⟨⟨NP.desc Q.g0 P.x ρ' hρ, Kap.desc Q.g0 ρ' hρ P.k κ' hκ, P.al, ?_, hb.1 P.b1, hb.2 P.b2, P.f, ?_⟩, rfl, rfl⟩` and prove the remaining obligations. Introduce `j`.

Take `⟨h1, h2⟩` from `P.eig j`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `e : (mat ρ') (Q.g0.p₀ (T.sg j)) = (mat P.x.ρ) (T.sg j)`. Rewrite using `[← hmat]`. Both sides reduce to the same expression.

Conclude with `e ▸ h2`. Use `⟨?_, fun v i => by rw [hψ]; exact P.maps.2 v i⟩` and prove the remaining obligations. Take `⟨-, -, -, -, hof, hsurj⟩` from `UpperTheory.V.Pa.comap_lam n P.x.A G0.G₀ Q.G0'.G₀ Q.g0.p₀ (GDet.ofRep (mat ρ'))`. Take `⟨-, -, -, hmap, -, -⟩` from `UpperTheory.V.Pa.comap_lam n B G0.G₀ Q.G0'.G₀ Q.g0.p₀ u'.D`. Apply `(hsurj (Glob.Hom.p₀_surj Q.g0)).1` to reduce the goal to its premises.

Rewrite using `[← hmap, hD, P.maps.1, hof (mat ρ'), hmat]`.
-/
theorem UpperTheory.V.Pa.pt_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Q : TWQuot T) (n : ℕ) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (r' : Resid Q.G0'.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (u' : Pair r' B) (D0 : ℕ) (P : Pt T u D0), Adapted T (r := r) → Glob.Compat Q.g0 r r' → u'.D.comap Q.g0.p₀ = u.D → u'.ψ = u.ψ → ∃ P' : Pt Q.grp u' D0, RingHom.ker P'.f = RingHom.ker P.f ∧ Nat.card P'.x.K = Nat.card P.x.K := by
  intro l _ L G0 T Q n O _ _ _ r r' B _ _ _ u u' D0 P hA hC hD hψ
  have hU := UpperTheory.V.Pa.pt_unip l L G0 T n O r B u D0 P hA
  obtain ⟨⟨ρ', hρ⟩, κ', hκ⟩ := UpperTheory.V.Pa.np_desc l L G0 Q.G0' Q.g0 n P.x P.k
    (T.H.toOpenSubgroup : Subgroup G0.Γ) T.H.toOpenSubgroup.isOpen'
    (fun g hg => MonoidHom.mem_ker.2 (T.H_η g hg)) hU Q.ker0
  have hb := UpperTheory.V.Pa.b_desc l L G0 T Q n P.x P.k ρ' hρ κ' hκ D0 hU
  letI := P.alg
  have hmat : (mat ρ').comp Q.g0.p₀ = mat P.x.ρ := by
    ext a i j
    simp [mat, hρ]
  refine ⟨⟨NP.desc Q.g0 P.x ρ' hρ, Kap.desc Q.g0 ρ' hρ P.k κ' hκ, P.al, ?_, hb.1 P.b1, hb.2 P.b2,
    P.f, ?_⟩, rfl, rfl⟩
  · intro j
    obtain ⟨h1, h2⟩ := P.eig j
    refine ⟨h1, ?_⟩
    have e : (mat ρ') (Q.g0.p₀ (T.sg j)) = (mat P.x.ρ) (T.sg j) := by
      rw [← hmat]
      rfl
    exact e ▸ h2
  · refine ⟨?_, fun v i => by rw [hψ]; exact P.maps.2 v i⟩
    obtain ⟨-, -, -, -, hof, hsurj⟩ := UpperTheory.V.Pa.comap_lam n P.x.A G0.G₀ Q.G0'.G₀ Q.g0.p₀
      (GDet.ofRep (mat ρ'))
    obtain ⟨-, -, -, hmap, -, -⟩ := UpperTheory.V.Pa.comap_lam n B G0.G₀ Q.G0'.G₀ Q.g0.p₀ u'.D
    apply (hsurj (Glob.Hom.p₀_surj Q.g0)).1
    rw [← hmap, hD, P.maps.1, hof (mat ρ'), hmat]
