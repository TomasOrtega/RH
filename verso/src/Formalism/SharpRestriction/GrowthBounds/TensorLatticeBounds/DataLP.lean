import Formalism.SharpRestriction.GrowthBounds.TensorLatticeBounds.DataLPa
import Formalism.SharpRestriction.GrowthBounds.TensorLatticeBounds.DataLPb
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.JOInjective

noncomputable section

namespace Formalism.MainNotions.G.Inhab

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

abbrev Z0 (n' : ℕ) : Fin n' → Fin (0 + 1) → ℤ := fun _ _ => 0

/- English proof (translation)
Unfold `Hten`. Use `one_mem_tensorLat O Kf _ fun s => ?_` and prove the remaining obligations. Rewrite using `[lamAt_zero]`. Conclude with `one_mem_H0_weight_zero O Kf _ _`.
-/
theorem one_mem_Hten (Λ : Fin n' → Submodule O (Fin (0 + 1) → Kf)) : (1 : MvPolynomial _ Kf) ∈ Hten O (Z0 n') Λ := by
  unfold Hten
  refine one_mem_tensorLat O Kf _ fun s => ?_
  rw [lamAt_zero]
  exact one_mem_H0_weight_zero O Kf _ _

def oneV (Kf : Type) [Field Kf] (n' : ℕ) : Vsp Kf (Z0 n') := ⟨1, one_mem_Vsp Kf⟩

def evV (Kf : Type) [Field Kf] (n' : ℕ) : Module.Dual Kf (Vsp Kf (Z0 n')) := (ccL Kf _).comp (Vsp Kf (Z0 n')).subtype

/- English proof (translation)
Use `show constantCoeff (1 : MvPolynomial _ Kf) = 1`. Simplify using the standard rewrite rules.
-/
theorem evV_oneV : evV Kf n' (oneV Kf n') = 1 := by
  show constantCoeff (1 : MvPolynomial _ Kf) = 1
  simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨x, hx, by subst hc; simp⟩`.
-/
theorem mem_scale_of_eq_one {X : Type} [AddCommGroup X] [Module Kf X] [Module O X] [IsScalarTower O Kf X] {c : Kf}
    (hc : c = 1) {M : Submodule O X} {x : X} (hx : x ∈ M) : x ∈ scale c M :=
  ⟨x, hx, by subst hc; simp⟩

/- English proof (translation)
The claim follows from `one_mem_Hten Λ`.
-/
theorem oneV_mem_toV (Λ : Fin n' → Submodule O (Fin (0 + 1) → Kf)) : oneV Kf n' ∈ toV (Z0 n') (Hten O (Z0 n') Λ) :=
  one_mem_Hten Λ

/- English proof (translation)
Introduce `v hv`. Conclude with `(mem_ccInt O Kf _).1 (Hten_le_ccInt O Kf Λ hΛ hv)`.
-/
theorem evV_mem_dual (Λ : Fin n' → Submodule O (Fin (0 + 1) → Kf)) (hΛ : ∀ s, IsLattice O (Λ s)) :
    evV Kf n' ∈ dualLat O Kf (toV (Z0 n') (Hten O (Z0 n') Λ)) := by
  intro v hv
  exact (mem_ccInt O Kf _).1 (Hten_le_ccInt O Kf Λ hΛ hv)

/- English proof (translation)
The claim follows from `LatticeSystems.je_extO_lat (gat1 h) (0 : Fin 1) s L hL`.
-/
theorem ext_lat (h : HidaSetting p n' W Qq O Kf ι σ j w) (L : Submodule W (Fin (0 + 1) → Qq)) (hL : IsLattice W L) (s : ℕ) :
    IsLattice O (extO O ι σ s L) :=
  LatticeSystems.je_extO_lat (gat1 h) (0 : Fin 1) s L hL

/- English proof (translation)
The claim follows from `LatticeSystems.je_LeAt_lat (gat1 h) (0 : Fin 1) s e he`.
-/
theorem Le_lat (h : HidaSetting p n' W Qq O Kf ι σ j w) (e : Edge W Qq (0 + 1)) (he : IsEdge p n' 1 e) (s : ℕ) :
    IsLattice O (LeAt p ι σ w s e) :=
  LatticeSystems.je_LeAt_lat (gat1 h) (0 : Fin 1) s e he

/- English proof (translation)
Rewrite using `[Ar_zero]`. Simplify using the standard rewrite rules.
-/
theorem w_pow_Ar : algebraMap O Kf w ^ (-Ar 1 (Z0 n')) = 1 := by
  rw [Ar_zero]; simp

/- English proof (translation)
Unfold `Nsrc`. Rewrite using `[Submodule.mem_inf]`. Use `⟨mem_scale_of_eq_one (by simp) (oneV_mem_toV _), ?_⟩` and prove the remaining obligations. Simplify using `only [Submodule.mem_iInf]`. Introduce `e _`.

Conclude with `mem_scale_of_eq_one w_pow_Ar (oneV_mem_toV _)`.
-/
theorem oneV_mem_Nsrc (L'' : Submodule W (Fin (0 + 1) → Qq)) :
    oneV Kf n' ∈ Nsrc p n' ι σ w 1 (Z0 n') 0 L'' := by
  unfold Nsrc
  rw [Submodule.mem_inf]
  refine ⟨mem_scale_of_eq_one (by simp) (oneV_mem_toV _), ?_⟩
  simp only [Submodule.mem_iInf]
  intro e _
  exact mem_scale_of_eq_one w_pow_Ar (oneV_mem_toV _)

/- English proof (translation)
Unfold `Ntgt`. Rewrite using `[Submodule.mem_inf]`. Use `⟨mem_scale_of_eq_one (by simp) (evV_mem_dual _ fun s => ext_lat h L hL s.val), ?_⟩` and prove the remaining obligations. Simplify using `only [Submodule.mem_iInf]`. Introduce `e he`.

Conclude with `mem_scale_of_eq_one w_pow_Ar (evV_mem_dual _ fun s => Le_lat h e he.1 s.val)`.
-/
theorem evV_mem_Ntgt (h : HidaSetting p n' W Qq O Kf ι σ j w) (L : Submodule W (Fin (0 + 1) → Qq)) (hL : IsLattice W L) :
    evV Kf n' ∈ Ntgt p n' ι σ w 1 (Z0 n') 0 L := by
  unfold Ntgt
  rw [Submodule.mem_inf]
  refine ⟨mem_scale_of_eq_one (by simp) (evV_mem_dual _ fun s => ext_lat h L hL s.val), ?_⟩
  simp only [Submodule.mem_iInf]
  intro e he
  exact mem_scale_of_eq_one w_pow_Ar (evV_mem_dual _ fun s => Le_lat h e he.1 s.val)

/- English proof (translation)
Use `⟨by norm_num, fun L hL => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `lat1 h L hL`. Use `⟨1, fun _ => edge1 W Qq p a, fun _ => oneV Kf n', fun _ => ⟨line_lattice_isEdge h a, rfl⟩, fun _ => oneV_mem_Nsrc _, ?_, 1, ?_, ?_⟩` and prove the remaining obligations. Introduce `_ e' he' hsrc hne`. It suffices to derive a contradiction.

Take `⟨b, rfl⟩` from `edge_eq h e' he'`. Establish `: b + 1 = a + 1` using `line_inj h hsrc`. Establish `hb : b = a` using `by omega`. Conclude with `hne (by rw [hb])`. Use `dimV_le_one Kf (n' := n') (m := 0)` as an intermediate fact.

Establish `h1 : (dimV Kf (Z0 n') : ℝ) ≤ 1` using `by exact_mod_cast this`. Simplify using `using h1`. Use `⟨(LinearMap.proj (0 : Fin 1)).smulRight (⟨evV Kf n', evV_mem_Ntgt h _ (line_isLattice h a)⟩ : ↥(Ntgt p n' ι σ w 1 (Z0 n') 0 (line W p a))), 1, ?_⟩` and prove the remaining obligations. Introduce `x i`. Establish `hi : i = 0` using `Subsingleton.elim _ _`.

Substitute `hi` using the available equality. Simplify using `only [Fin.sum_univ_one, Matrix.one_apply_eq, map_one, one_mul, pow_zero]`. Use `show (x 0 • evV Kf n') (((p : Kf) ^ Ar 1 (Z0 n')) • oneV Kf n') = _`. Rewrite using `[Ar_zero, zpow_zero, one_smul, LinearMap.smul_apply, evV_oneV, Algebra.smul_def, mul_one]`.
-/
theorem lpprime_zero (h : HidaSetting p n' W Qq O Kf ι σ j w) :
    LPprime (W := W) p n' ι σ w 1 (Z0 n') 0 0 0 4 := by
  refine ⟨by norm_num, fun L hL => ?_⟩
  obtain ⟨a, rfl⟩ := lat1 h L hL
  refine ⟨1, fun _ => edge1 W Qq p a, fun _ => oneV Kf n', fun _ => ⟨line_lattice_isEdge h a, rfl⟩,
    fun _ => oneV_mem_Nsrc _, ?_, 1, ?_, ?_⟩
  · intro _ e' he' hsrc hne
    exfalso
    obtain ⟨b, rfl⟩ := edge_eq h e' he'
    have : b + 1 = a + 1 := line_inj h hsrc
    have hb : b = a := by omega
    exact hne (by rw [hb])
  · have := dimV_le_one Kf (n' := n') (m := 0)
    have h1 : (dimV Kf (Z0 n') : ℝ) ≤ 1 := by exact_mod_cast this
    simpa using h1
  · refine ⟨(LinearMap.proj (0 : Fin 1)).smulRight
      (⟨evV Kf n', evV_mem_Ntgt h _ (line_isLattice h a)⟩ : ↥(Ntgt p n' ι σ w 1 (Z0 n') 0 (line W p a))), 1, ?_⟩
    intro x i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp only [Fin.sum_univ_one, Matrix.one_apply_eq, map_one, one_mul, pow_zero]
    show (x 0 • evV Kf n') (((p : Kf) ^ Ar 1 (Z0 n')) • oneV Kf n') = _
    rw [Ar_zero, zpow_zero, one_smul, LinearMap.smul_apply, evV_oneV, Algebra.smul_def, mul_one]

/- English proof (translation)
Establish `: Fact p.Prime` using `⟨hp⟩`. Establish `hS` using `Formalism.L2.G.settingStd p n' h5 h2 he`. Establish `h` using `hS.1`. Take `⟨F, -, h2, h3⟩` from `exists_integral_nonzero_form h`. Use `⟨gat1 h, le_rfl, rfl, fun _ => level1_trivStab h, fun _ => level1_finClasses h, ?_, fun _ => ⟨hS, lpprime_zero h⟩⟩` and prove the remaining obligations.

Introduce `hb`. Rewrite `h2` using `[hb]`. Conclude with `h3 ((Submodule.mem_bot _).1 h2)`.
-/
theorem gat_lp_nonempty (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (n' : ℕ) (h2 : 2 ≤ n') (he : Even n') :
    ∃ G : GAtP p, 1 ≤ G.P.nV ∧ G.P.r = 1 ∧ G.TrivStab ∧ G.FinClasses ∧ G.Mna ≠ ⊥ ∧
      ∀ v, UnramifiedQuadraticSetting p (G.P.n' v) (G.P.W v) (G.P.Qq v) G.O G.Kf (G.P.ι v) (G.P.σ v) (G.P.j v) G.P.w ∧
        LPprime (W := G.P.W v) (Qq := G.P.Qq v) (O := G.O) (Kf := G.Kf) p (G.P.n' v) (G.P.ι v) (G.P.σ v) G.P.w G.P.r
          (G.P.lam0 v) 0 0 0 4 := by
  have : Fact p.Prime := ⟨hp⟩
  have hS := Formalism.L2.G.settingStd p n' h5 h2 he
  have h := hS.1
  obtain ⟨F, -, h2, h3⟩ := exists_integral_nonzero_form h
  refine ⟨gat1 h, le_rfl, rfl, fun _ => level1_trivStab h, fun _ => level1_finClasses h, ?_,
    fun _ => ⟨hS, lpprime_zero h⟩⟩
  intro hb; rw [hb] at h2; exact h3 ((Submodule.mem_bot _).1 h2)

end Formalism.MainNotions.G.Inhab

end
