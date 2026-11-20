import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZphiPowPr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinFam

namespace AffZphi

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

/- English proof (translation)
Unfold `mkZ pa`. Rewrite using `[lift_fst_assoc]`. Conclude with `(Out.powIsLimit A 4).fac _ ⟨i⟩`.
-/
theorem mkZ_pa {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (i : Fin 4) :
    mkZ A B u v ≫ pa A B i = u i := by
  unfold mkZ pa
  rw [lift_fst_assoc]
  exact (Out.powIsLimit A 4).fac _ ⟨i⟩

/- English proof (translation)
Unfold `mkZ pb`. Rewrite using `[lift_snd_assoc]`. Conclude with `(Out.powIsLimit B 4).fac _ ⟨j⟩`.
-/
theorem mkZ_pb {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (j : Fin 4) :
    mkZ A B u v ≫ pb A B j = v j := by
  unfold mkZ pb
  rw [lift_snd_assoc]
  exact (Out.powIsLimit B 4).fac _ ⟨j⟩

/- English proof (translation)
Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Conclude with `(Out.powIsLimit A 4).hom_ext fun ⟨i⟩ => by simpa [pa] using ha i`. Conclude with `(Out.powIsLimit B 4).hom_ext fun ⟨j⟩ => by simpa [pb] using hb j`.
-/
theorem zob_ext {T : Over S} (f g : T ⟶ Zob A B) (ha : ∀ i, f ≫ pa A B i = g ≫ pa A B i)
    (hb : ∀ j, f ≫ pb A B j = g ≫ pb A B j) : f = g := by
  apply CartesianMonoidalCategory.hom_ext
  · exact (Out.powIsLimit A 4).hom_ext fun ⟨i⟩ => by simpa [pa] using ha i
  · exact (Out.powIsLimit B 4).hom_ext fun ⟨j⟩ => by simpa [pb] using hb j

instance pa_isMonHom (i : Fin 4) : IsMonHom (pa A B i) := by unfold pa; infer_instance

instance pb_isMonHom (j : Fin 4) : IsMonHom (pb A B j) := by unfold pb; infer_instance

/- English proof (translation)
Apply the tactic sequence `fin_cases i <;> rfl`.
-/
theorem sig_castAdd (i : Fin 4) : sig (Fin.castAdd 4 i) = .inl i := by fin_cases i <;> rfl

/- English proof (translation)
Apply the tactic sequence `fin_cases j <;> rfl`.
-/
theorem sig_natAdd (j : Fin 4) : sig (Fin.natAdd 4 j) = .inr j := by fin_cases j <;> rfl

end AffZphi

open AffZphi

/- English proof (translation)
Introduce `h M d S t c B _ _ Q la mu hZ _ hu`. Establish `hB : IsAbelianScheme B` using `hZ.1`. Establish `hA : IsAbelianScheme c.A` using `c.ab`. Establish `hZab : IsAbelianScheme (Zob c.A B)` using `AbelianSchemeGerms.isAbelianScheme_tensor _ _ (AbelianSchemeGerms.isAbelianScheme_powObj c.A hA 3) (AbelianSchemeGerms.isAbelianScheme_powObj B hB 3)`. Establish `h8 : IsAbelianScheme (Out.powObj c.A 8)` using `AbelianSchemeGerms.isAbelianScheme_powObj c.A hA 7`.

Use `hZab.comm` as an intermediate fact. Use `hZab.smooth` as an intermediate fact. Use `hZab.proper` as an intermediate fact. Use `h8.proper` as an intermediate fact. Establish `hfin : IsFinite ((𝟙 (Zob c.A B)) ^ d).left` using `GlobalTheory.GrpTangent.isFinite_id_pow _ hu`.

Establish `hlm : mu ≫ la = 𝟙 B ^ d` using `hZ.2.2.2.2.2.2.1`. Set `ν : Out.powObj c.A 8 ⟶ Zob c.A B` to `mkZ c.A B (fun i => Out.powPr c.A (Fin.castAdd 4 i) ^ d) (fun j => Out.powPr c.A (Fin.natAdd 4 j) ≫ la)`. Establish `key : zphi c.A B mu ≫ ν = (𝟙 (Zob c.A B)) ^ d`. Use `zob_ext c.A B _ _ (fun i => ?_) (fun j => ?_)` and prove the remaining obligations. Rewrite using `[Category.assoc, mkZ_pa, MonObj.comp_pow, zphi_powPr, MonObj.pow_comp, Category.id_comp]`.

Simplify using `[zpr, sig_castAdd]`. Rewrite using `[Category.assoc, mkZ_pb, ← Category.assoc, zphi_powPr, MonObj.pow_comp, Category.id_comp]`. Simplify using `only [zpr, sig_natAdd, Sum.elim_inr, Category.assoc, hlm, MonObj.comp_pow, Category.comp_id]`. Establish `hsep : IsSeparated ν.left`. Establish `: IsSeparated (ν.left ≫ (Zob c.A B).hom)` using `by rw [Over.w ν]; infer_instance`.

Conclude with `IsSeparated.of_comp ν.left (Zob c.A B).hom`. Establish `: IsAffineHom ((zphi c.A B mu).left ≫ ν.left)`. Rewrite using `[← Over.comp_left, key]`. Use `infer_instance`. Conclude with `IsAffineHom.of_comp _ ν.left`.
-/
theorem isAffineHom_zphi : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t)
    (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A)
    (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 0 < d → IsUnit ((d : ℕ) : Γ(S, ⊤)) →
    IsAffineHom (GlobalTheory.ZarhinFam.zphi c.A B mu).left := by
  intro h M d S t c B _ _ Q la mu hZ _ hu
  have hB : IsAbelianScheme B := hZ.1
  have hA : IsAbelianScheme c.A := c.ab
  have hZab : IsAbelianScheme (Zob c.A B) := AbelianSchemeGerms.isAbelianScheme_tensor _ _
    (AbelianSchemeGerms.isAbelianScheme_powObj c.A hA 3) (AbelianSchemeGerms.isAbelianScheme_powObj B hB 3)
  have h8 : IsAbelianScheme (Out.powObj c.A 8) := AbelianSchemeGerms.isAbelianScheme_powObj c.A hA 7
  have := hZab.comm
  have := hZab.smooth
  have := hZab.proper
  have := h8.proper
  have hfin : IsFinite ((𝟙 (Zob c.A B)) ^ d).left := GlobalTheory.GrpTangent.isFinite_id_pow _ hu
  have hlm : mu ≫ la = 𝟙 B ^ d := hZ.2.2.2.2.2.2.1
  let ν : Out.powObj c.A 8 ⟶ Zob c.A B :=
    mkZ c.A B (fun i => Out.powPr c.A (Fin.castAdd 4 i) ^ d) (fun j => Out.powPr c.A (Fin.natAdd 4 j) ≫ la)
  have key : zphi c.A B mu ≫ ν = (𝟙 (Zob c.A B)) ^ d := by
    refine zob_ext c.A B _ _ (fun i => ?_) (fun j => ?_)
    · rw [Category.assoc, mkZ_pa, MonObj.comp_pow, zphi_powPr, MonObj.pow_comp, Category.id_comp]
      simp [zpr, sig_castAdd]
    · rw [Category.assoc, mkZ_pb, ← Category.assoc, zphi_powPr, MonObj.pow_comp, Category.id_comp]
      simp only [zpr, sig_natAdd, Sum.elim_inr, Category.assoc, hlm, MonObj.comp_pow, Category.comp_id]
  have hsep : IsSeparated ν.left := by
    have : IsSeparated (ν.left ≫ (Zob c.A B).hom) := by rw [Over.w ν]; infer_instance
    exact IsSeparated.of_comp ν.left (Zob c.A B).hom
  have : IsAffineHom ((zphi c.A B mu).left ≫ ν.left) := by
    rw [← Over.comp_left, key]; infer_instance
  exact IsAffineHom.of_comp _ ν.left

end GlobalTheory.ZarhinFam
