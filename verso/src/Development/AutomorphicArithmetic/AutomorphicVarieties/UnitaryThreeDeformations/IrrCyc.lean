import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IrrOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostOk
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CzBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Clifford

open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

/- English proof (translation)
Rewrite using `[totallyDisconnectedSpace_iff_connectedComponent_one]`. Use `Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `QuotientGroup.mk_surjective y`. Assume the negation of the conclusion as `hx`. Establish `hx' : x ∉ N` using `fun h => hx ((QuotientGroup.eq_one_iff x).2 h)`.

Establish `ho : IsOpen {g : G | g * x ∉ N}` using `hN.isOpen_compl.preimage (continuous_mul_const x)`. Take `⟨U, hU⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')`. Set `V : Subgroup (G ⧸ N)` to `U.toSubgroup.map (QuotientGroup.mk' N)`. Establish `hVo : IsOpen (V : Set (G ⧸ N))` using `QuotientGroup.isOpenMap_coe _ U.isOpen'`. Establish `hV : IsClopen (V : Set (G ⧸ N))` using `⟨V.isClosed_of_isOpen hVo, hVo⟩`.

Take `⟨u, hu, hux⟩` from `hV.connectedComponent_subset V.one_mem hy`. Conclude with `hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)`.
-/
private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  by_contra hx
  have hx' : x ∉ N := fun h => hx ((QuotientGroup.eq_one_iff x).2 h)
  have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
  let V : Subgroup (G ⧸ N) := U.toSubgroup.map (QuotientGroup.mk' N)
  have hVo : IsOpen (V : Set (G ⧸ N)) := QuotientGroup.isOpenMap_coe _ U.isOpen'
  have hV : IsClopen (V : Set (G ⧸ N)) := ⟨V.isClosed_of_isOpen hVo, hVo⟩
  obtain ⟨u, hu, hux⟩ := hV.connectedComponent_subset V.one_mem hy
  exact hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)

/- English proof (translation)
Take `⟨x, hx⟩` from `Module.End.exists_eigenvalue (Matrix.toLin' M)`. Establish `htop : Module.End.eigenspace (Matrix.toLin' M) x = ⊤`. Use `(h _ fun g hg v hv => ?_).resolve_left hx` and prove the remaining obligations. Rewrite `hv`, the goal using `[Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]`. Rewrite using `[Matrix.mulVec_mulVec, hM g hg, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]`.

Use `⟨x, Matrix.toLin'.injective (LinearMap.ext fun v => ?_)⟩` and prove the remaining obligations. Establish `: v ∈ Module.End.eigenspace (Matrix.toLin' M) x` using `by rw [htop]; trivial`. Rewrite using `[Module.End.mem_eigenspace_iff.1 this]`. Simplify using the standard rewrite rules.
-/
private theorem schur {G κ : Type} [Group G] [Field κ] [IsAlgClosed κ] {m : ℕ} [NeZero m] (U : Subgroup G)
    (a : G → Matrix (Fin m) (Fin m) κ) (h : MatIrr U a) (M : Matrix (Fin m) (Fin m) κ)
    (hM : ∀ g ∈ U, M * a g = a g * M) : ∃ x : κ, M = x • 1 := by
  obtain ⟨x, hx⟩ := Module.End.exists_eigenvalue (Matrix.toLin' M)
  have htop : Module.End.eigenspace (Matrix.toLin' M) x = ⊤ := by
    refine (h _ fun g hg v hv => ?_).resolve_left hx
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, hM g hg, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  refine ⟨x, Matrix.toLin'.injective (LinearMap.ext fun v => ?_)⟩
  have : v ∈ Module.End.eigenspace (Matrix.toLin' M) x := by rw [htop]; trivial
  rw [Module.End.mem_eigenspace_iff.1 this]
  simp

/- English proof (translation)
Assume the negation of the conclusion as `hred`. Set `ρ` to `glPart η r hm`. Establish `hρ : ∀ g : η.ker, (ρ g : Matrix (Fin 3) (Fin 3) κ) = mats r g` using `fun _ => rfl`. Take `⟨φ, hφ1, -, hφ3, M, hM⟩` from `exists_selfTwist ρ (χ.comp η.ker.subtype).ker (fun a b => by simp [MonoidHom.mem_ker, mul_right_comm]) (fun W hW => ho _ hη le_rfl W fun g hg => hW ⟨g, hg⟩ trivial) (fun h => hred fun W hW => h W fun g hg => hW g ⟨g.2, hg⟩)`. Establish `hiff : ∀ g, φ g = 1 ↔ (M : Matrix (Fin 3) (Fin 3) κ) * mats r g = mats r g * M`.

Introduce `g`. Establish `h1` using `hM g trivial`. Simplify using `only [hρ] at h1`. Use `⟨fun h => by simpa [h] using h1, fun h => ?_⟩` and prove the remaining obligations. Rewrite `h1` using `[← h, Matrix.mul_smul]`.

Establish `hu : IsUnit ((M : Matrix (Fin 3) (Fin 3) κ) * mats r g)` using `(M * ρ g).isUnit`. Conclude with `Units.ext (smul_left_injective κ hu.ne_zero (h1.trans (one_smul _ _).symm))`. Establish `hcl : IsClosed (φ.ker : Set η.ker)`. Establish `: (φ.ker : Set η.ker) = {g : η.ker | (M : Matrix (Fin 3) (Fin 3) κ) * mats r g = mats r g * M}` using `Set.ext hiff`. Rewrite using `[this]`.

Establish `hc'` using `hc.comp (continuous_subtype_val (p := fun g => g ∈ η.ker))`. Conclude with `isClosed_eq (continuous_const.mul hc') (hc'.mul continuous_const)`. Use `haveI : φ.ker.FiniteIndex := by haveI : Finite φ.range := Finite.of_injective (fun x => (⟨x.1, by`. Take `⟨_, g, rfl⟩` from `x`. Conclude with `DFunLike.congr_fun hφ3 g⟩ : rootsOfUnity 3 κ))`.

Use the proof step `(fun x y h => Subtype.ext (Subtype.mk.inj h))`. Conclude with `Subgroup.finiteIndex_ker φ`. Establish `hop : IsOpen (φ.ker.map η.ker.subtype : Set G)` using `hη.isOpenMap_subtype_val _ (Subgroup.isOpen_of_isClosed_of_finiteIndex (G := η.ker) φ.ker hcl)`. Take `⟨x, hx⟩` from `schur _ _ (ho _ hop (Subgroup.map_subtype_le _)) M (by`. Introduce and unpack `_ ⟨g, hg, rfl⟩`.

Conclude with `(hiff g).1 hg)`. Conclude with `hφ1 (MonoidHom.ext fun g => (hiff g).2 (by simp [hx]))`.
-/
private theorem abs_irr {G κ B : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [Field κ] [IsAlgClosed κ] [CharZero κ] [TopologicalSpace κ] [IsTopologicalRing κ] [T2Space κ] [CommGroup B]
    (η : G →* ℤˣ) (hη : IsOpen (η.ker : Set G)) (r : G →* GG 3 κ) (hm : HasMult η r) (hc : Continuous (mats r))
    (χ : G →* B) (ho : ∀ U : Subgroup G, IsOpen (U : Set G) → U ≤ η.ker → MatIrr U (mats r)) :
    MatIrr (η.ker ⊓ χ.ker) (mats r) := by
  by_contra hred
  let ρ := glPart η r hm
  have hρ : ∀ g : η.ker, (ρ g : Matrix (Fin 3) (Fin 3) κ) = mats r g := fun _ => rfl
  obtain ⟨φ, hφ1, -, hφ3, M, hM⟩ := exists_selfTwist ρ (χ.comp η.ker.subtype).ker
    (fun a b => by simp [MonoidHom.mem_ker, mul_right_comm])
    (fun W hW => ho _ hη le_rfl W fun g hg => hW ⟨g, hg⟩ trivial)
    (fun h => hred fun W hW => h W fun g hg => hW g ⟨g.2, hg⟩)
  have hiff : ∀ g, φ g = 1 ↔ (M : Matrix (Fin 3) (Fin 3) κ) * mats r g = mats r g * M := by
    intro g
    have h1 := hM g trivial
    simp only [hρ] at h1
    refine ⟨fun h => by simpa [h] using h1, fun h => ?_⟩
    rw [← h, Matrix.mul_smul] at h1
    have hu : IsUnit ((M : Matrix (Fin 3) (Fin 3) κ) * mats r g) := (M * ρ g).isUnit
    exact Units.ext (smul_left_injective κ hu.ne_zero (h1.trans (one_smul _ _).symm))
  have hcl : IsClosed (φ.ker : Set η.ker) := by
    have : (φ.ker : Set η.ker) = {g : η.ker | (M : Matrix (Fin 3) (Fin 3) κ) * mats r g = mats r g * M} :=
      Set.ext hiff
    rw [this]
    have hc' := hc.comp (continuous_subtype_val (p := fun g => g ∈ η.ker))
    exact isClosed_eq (continuous_const.mul hc') (hc'.mul continuous_const)
  haveI : φ.ker.FiniteIndex := by
    haveI : Finite φ.range := Finite.of_injective
      (fun x => (⟨x.1, by
        obtain ⟨_, g, rfl⟩ := x
        exact DFunLike.congr_fun hφ3 g⟩ : rootsOfUnity 3 κ))
      (fun x y h => Subtype.ext (Subtype.mk.inj h))
    exact Subgroup.finiteIndex_ker φ
  have hop : IsOpen (φ.ker.map η.ker.subtype : Set G) :=
    hη.isOpenMap_subtype_val _ (Subgroup.isOpen_of_isClosed_of_finiteIndex (G := η.ker) φ.ker hcl)
  obtain ⟨x, hx⟩ := schur _ _ (ho _ hop (Subgroup.map_subtype_le _)) M (by
    rintro _ ⟨g, hg, rfl⟩
    exact (hiff g).1 hg)
  exact hφ1 (MonoidHom.ext fun g => (hiff g).2 (by simp [hx]))

/- English proof (translation)
Introduce `Ω _ _ _ l _ c N _ e ψ o₁ h S A F hF g₁ hg r hr hI`. Establish `hok` using `hostFrame_ok Ω c e ψ o₁ h S A F hF`. Use `haveI hcl := isClosed_NS Ω (S : Set Pl)`. Use `haveI : TotallyDisconnectedSpace (Gam Ω S) := totDisc_quot _ hcl`. Take `⟨hm, -, hc, -⟩` from `isCharZeroPt_basic F hok g₁ hg r hr`.

Establish `hη : ∀ s, F.η (toGS Ω _ s) = eta4 Ω s` using `fun s => by rw [← hF.η, hF.π]; rfl`. Use `abs_irr (eta4 Ω) ?_ (r.comp (toGS Ω _)) (fun s => (hm _).trans (hη s)) (hc.comp (continuous_toGS Ω _)) (cycZ ℚ Ω l) (matIrr_open Ω c e ψ o₁ h S A F hF g₁ hg r hr hI)` and prove the remaining obligations. Rewrite using `[← hF.η]`. Conclude with `(hok.η_cont.comp_continuous hok.π_cont).isOpen_fiber 1`.
-/
theorem UpperTheory.V.UnitaryThreeInertia.matIrr_cyc :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
    ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
    ∀ (g₁ : Gam Ω S), F.Marked g₁ → ∀ r : Gam Ω S →* GG 3 (PadicAlgCl l), F.IsCharZeroPt g₁ r → TypeI F.η r → MatIrr ((eta4 Ω).ker ⊓ (cycZ ℚ Ω l).ker) fun s => (r (toGS Ω _ s)).mat := by
  intro Ω _ _ _ l _ c N _ e ψ o₁ h S A F hF g₁ hg r hr hI
  have hok := hostFrame_ok Ω c e ψ o₁ h S A F hF
  haveI hcl := isClosed_NS Ω (S : Set Pl)
  haveI : TotallyDisconnectedSpace (Gam Ω S) := totDisc_quot _ hcl
  obtain ⟨hm, -, hc, -⟩ := isCharZeroPt_basic F hok g₁ hg r hr
  have hη : ∀ s, F.η (toGS Ω _ s) = eta4 Ω s := fun s => by rw [← hF.η, hF.π]; rfl
  refine abs_irr (eta4 Ω) ?_ (r.comp (toGS Ω _)) (fun s => (hm _).trans (hη s)) (hc.comp (continuous_toGS Ω _))
    (cycZ ℚ Ω l) (matIrr_open Ω c e ψ o₁ h S A F hF g₁ hg r hr hI)
  rw [← hF.η]
  exact (hok.η_cont.comp_continuous hok.π_cont).isOpen_fiber 1
