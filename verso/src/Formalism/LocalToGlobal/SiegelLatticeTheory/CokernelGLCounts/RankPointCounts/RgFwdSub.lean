import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RGHyp

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG4

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

/- English proof (translation)
Use `set c : E := algebraMap F E (g.q : F) with hc`. Establish `hcO : c ∈ M.L.O` using `q_mem_O g`. Establish `hcL : ∀ (Λ : Submodule M.L.O V) {x : V}, x ∈ Λ → c • x ∈ Λ`. Introduce `Λ x hx`. Conclude with `Λ.smul_mem (⟨c, hcO⟩ : M.L.O) hx`.

Establish `hMMU : ∀ (t : Term V M r) {x : V}, x ∈ MMsharp H t → x ∈ Submodule.span E (Set.range (Sum.elim t.f t.f'))`. Introduce `t x hx`. Establish `h1 : x ∈ Submodule.span E (Set.range (H.MMfam t))` using `hx.1`. Use `Submodule.span_le.mpr ?_ h1` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`.

Establish `hle : H.Xp t.f ⊔ H.Xp t.f' ≤ Submodule.span E (Set.range (Sum.elim t.f t.f'))` using `sup_le (Submodule.span_mono (by`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `⟨Sum.inl j, rfl⟩))`. Use the proof step `(Submodule.span_mono (by`. Introduce and unpack `_ ⟨j, rfl⟩`.

Conclude with `⟨Sum.inr j, rfl⟩))`. Conclude with `hle (MMfam_mem_sup H t i)`. Introduce and unpack `_ ⟨p, ⟨u, u', u'', hu, hu', hd, rfl⟩, rfl⟩`. Take `⟨w, hw⟩` from `D.hsurj₁ u`. Take `⟨w'', hw''⟩` from `D.hsurj₁ u''`.

Take `⟨w', hw'c⟩ : ∃ w' : ↥(H.W0 t₁.f t₁.f'), (w' : V) = (w : V) - c • (w'' : V)` from `⟨w - c • w'', rfl⟩`. Establish `hw'eq : w' = w - c • w''` using `Subtype.ext (by rw [hw'c]; rfl)`. Establish `hψw' : (ψ w' : V) = (ψ w : V) - c • (ψ w'' : V)`. Rewrite using `[hw'eq, map_sub, map_smul]`. Both sides reduce to the same expression.

Establish `hx : (u : V) + w ∈ H.perp (H.X t₁.f)` using `Submodule.add_mem _ hu (mem_perp_isotropicSpan_of_mem_framePerp H w.2)`. Establish `hx' : (u' : V) + w' ∈ H.perp (H.X t₁.f')` using `Submodule.add_mem _ hu' (mem_perp_isotropicSpan_of_mem_framePerp' H w'.2)`. Establish `hxL' : (u' : V) + w' ∈ t₁.abelian₂`. Establish `e : (u' : V) + w' = ((u : V) + w) - c • ((u'' : V) + w'')`. Rewrite using `[hw'c, smul_add, ← hd]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `Submodule.sub_mem _ hw (hcL _ hw'')`. Establish `hdiffL : ((u : V) + w) - ((u' : V) + w') ∈ H.smulLat c t₁.abelian₂`. Establish `e : ((u : V) + w) - ((u' : V) + w') = c • ((u'' : V) + w'')`.

Rewrite using `[hw'c, smul_add, ← hd]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `Submodule.subset_span ⟨_, hw'', rfl⟩`. Establish `hmem : (φ' (H.mkW t₁.f' ⟨_, hx'⟩), φ (H.mkW t₁.f ⟨_, hx⟩)) ∈ H.iotaGraph g ⟨Λ₂, t₂.f, t₂.f', t₂.T, t₂.T'⟩`.

Rewrite using `[← hI]`. Conclude with `⟨_, ⟨⟨_, hx'⟩, ⟨_, hx⟩, hxL', hw, hdiffL, rfl⟩, rfl⟩`. Take `⟨y', y, hy'L, hyL, hyd, hyeq⟩` from `hmem`. Rewrite `hyeq` using `[Prod.mk.injEq]`. Take `⟨hyeq', hyeq2⟩` from `hyeq`.

Take `⟨z, hzL, hz⟩` from `exists_of_mem_smulLat H hyd`. Take `⟨a, ha, b, hb, hab⟩` from `dec_of D.hU₂ (y : V)`. Take `⟨a', ha', b', hb', hab'⟩` from `dec_of D.hU₂ (y' : V)`. Take `⟨a'', ha'', b'', hb'', hab''⟩` from `dec_of D.hU₂ z`. Establish `hx₂ : a + b ∈ H.perp (H.X t₂.f)`.

Rewrite using `[hab]`. Conclude with `y.2`. Establish `hx₂' : a' + b' ∈ H.perp (H.X t₂.f')`. Rewrite using `[hab']`. Conclude with `y'.2`.

Establish `hap : a ∈ H.perp (H.X t₂.f)` using `perp_left H (mem_perp_isotropicSpan_of_mem_framePerp H hb) hx₂`. Establish `hap' : a' ∈ H.perp (H.X t₂.f')` using `perp_left H (mem_perp_isotropicSpan_of_mem_framePerp' H hb') hx₂'`. Establish `h1 : φ (H.mkW t₁.f ⟨_, hx⟩) = H.mkW t₂.f ⟨a + b, hx₂⟩` using `hyeq2.trans (congrArg _ (Subtype.ext hab.symm))`. Establish `h1' : φ' (H.mkW t₁.f' ⟨_, hx'⟩) = H.mkW t₂.f' ⟨a' + b', hx₂'⟩` using `hyeq'.trans (congrArg _ (Subtype.ext hab'.symm))`. Take `⟨hbψ, hφ⟩` from `RGHyp.trF H D (hMMU t₁ u.2) hu w hx ha hb hap hx₂ h1`.

Take `⟨hb'ψ, hφ'⟩` from `RGHyp.trF' H D (hMMU t₁ u'.2) hu' w' hx' ha' hb' hap' hx₂' h1'`. Take `⟨hda, hdb⟩` from `dec_diff D.hU₂ c ha ha' ha'' hb hb' hb'' hab hab' hab'' hz`. Establish `hb''ψ : b'' = ψ w''`. Apply `smul_cancel_q g` to reduce the goal to its premises. Rewrite using `[← hdb, hbψ, hb'ψ, hψw']`.

Normalize the expressions using the abelian group laws. Establish `haM : a ∈ MMsharp H t₂` using `part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha hb (by rw [hab]; exact hyL)`. Establish `ha'M : a' ∈ MMsharp H t₂` using `part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha' hb' (by rw [hab']; exact hy'L)`. Establish `ha''M : a'' ∈ MMsharp H t₂` using `part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha'' hb'' (by rw [hab'']; exact hzL)`. Use `⟨⟨a, haM⟩, ⟨a', ha'M⟩, ⟨a'', ha''M⟩, hap, hap', hda, ?_⟩` and prove the remaining obligations.

Use `Prod.ext ?_ (Prod.ext ?_ (Prod.ext hφ hφ'))` and prove the remaining obligations. Conclude with `(D.hθ u ⟨a, haM⟩).mpr ⟨w, hw, by rw [← hbψ, hab]; exact hyL⟩`. Conclude with `(D.hθ u'' ⟨a'', ha''M⟩).mpr ⟨w'', hw'', by rw [← hb''ψ, hab'']; exact hzL⟩`.
-/
theorem rg_fwd_sub (g : SplitG M.L) {t₁ t₂ : Term V M r} {Λ₂ : Submodule M.L.O V}
    {ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f')} {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂}
    {φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'} (D : RGHyp H t₁ t₂ Λ₂ ψ θ φ φ')
    (hI : Prod.map φ' φ '' H.iotaGraph g t₁ = H.iotaGraph g ⟨Λ₂, t₂.f, t₂.f', t₂.T, t₂.T'⟩) :
    (fun p => (θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2)) '' GamR H t₁ (algebraMap F E (g.q : F)) ⊆
      GamR H t₂ (algebraMap F E (g.q : F)) := by
  set c : E := algebraMap F E (g.q : F) with hc
  have hcO : c ∈ M.L.O := q_mem_O g
  have hcL : ∀ (Λ : Submodule M.L.O V) {x : V}, x ∈ Λ → c • x ∈ Λ := by
    intro Λ x hx
    exact Λ.smul_mem (⟨c, hcO⟩ : M.L.O) hx
  have hMMU : ∀ (t : Term V M r) {x : V}, x ∈ MMsharp H t →
      x ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) := by
    intro t x hx
    have h1 : x ∈ Submodule.span E (Set.range (H.MMfam t)) := hx.1
    refine Submodule.span_le.mpr ?_ h1
    rintro _ ⟨i, rfl⟩
    have hle : H.Xp t.f ⊔ H.Xp t.f' ≤ Submodule.span E (Set.range (Sum.elim t.f t.f')) :=
      sup_le
        (Submodule.span_mono (by
          rintro _ ⟨j, rfl⟩
          exact ⟨Sum.inl j, rfl⟩))
        (Submodule.span_mono (by
          rintro _ ⟨j, rfl⟩
          exact ⟨Sum.inr j, rfl⟩))
    exact hle (MMfam_mem_sup H t i)
  rintro _ ⟨p, ⟨u, u', u'', hu, hu', hd, rfl⟩, rfl⟩
  obtain ⟨w, hw⟩ := D.hsurj₁ u
  obtain ⟨w'', hw''⟩ := D.hsurj₁ u''
  obtain ⟨w', hw'c⟩ : ∃ w' : ↥(H.W0 t₁.f t₁.f'), (w' : V) = (w : V) - c • (w'' : V) :=
    ⟨w - c • w'', rfl⟩
  have hw'eq : w' = w - c • w'' := Subtype.ext (by rw [hw'c]; rfl)
  have hψw' : (ψ w' : V) = (ψ w : V) - c • (ψ w'' : V) := by
    rw [hw'eq, map_sub, map_smul]
    rfl
  have hx : (u : V) + w ∈ H.perp (H.X t₁.f) := Submodule.add_mem _ hu (mem_perp_isotropicSpan_of_mem_framePerp H w.2)
  have hx' : (u' : V) + w' ∈ H.perp (H.X t₁.f') := Submodule.add_mem _ hu' (mem_perp_isotropicSpan_of_mem_framePerp' H w'.2)
  have hxL' : (u' : V) + w' ∈ t₁.abelian₂ := by
    have e : (u' : V) + w' = ((u : V) + w) - c • ((u'' : V) + w'') := by
      rw [hw'c, smul_add, ← hd]
      abel
    rw [e]
    exact Submodule.sub_mem _ hw (hcL _ hw'')
  have hdiffL : ((u : V) + w) - ((u' : V) + w') ∈ H.smulLat c t₁.abelian₂ := by
    have e : ((u : V) + w) - ((u' : V) + w') = c • ((u'' : V) + w'') := by
      rw [hw'c, smul_add, ← hd]
      abel
    rw [e]
    exact Submodule.subset_span ⟨_, hw'', rfl⟩
  have hmem : (φ' (H.mkW t₁.f' ⟨_, hx'⟩), φ (H.mkW t₁.f ⟨_, hx⟩)) ∈
      H.iotaGraph g ⟨Λ₂, t₂.f, t₂.f', t₂.T, t₂.T'⟩ := by
    rw [← hI]
    exact ⟨_, ⟨⟨_, hx'⟩, ⟨_, hx⟩, hxL', hw, hdiffL, rfl⟩, rfl⟩
  obtain ⟨y', y, hy'L, hyL, hyd, hyeq⟩ := hmem
  rw [Prod.mk.injEq] at hyeq
  obtain ⟨hyeq', hyeq2⟩ := hyeq
  obtain ⟨z, hzL, hz⟩ := exists_of_mem_smulLat H hyd
  obtain ⟨a, ha, b, hb, hab⟩ := dec_of D.hU₂ (y : V)
  obtain ⟨a', ha', b', hb', hab'⟩ := dec_of D.hU₂ (y' : V)
  obtain ⟨a'', ha'', b'', hb'', hab''⟩ := dec_of D.hU₂ z
  have hx₂ : a + b ∈ H.perp (H.X t₂.f) := by
    rw [hab]
    exact y.2
  have hx₂' : a' + b' ∈ H.perp (H.X t₂.f') := by
    rw [hab']
    exact y'.2
  have hap : a ∈ H.perp (H.X t₂.f) := perp_left H (mem_perp_isotropicSpan_of_mem_framePerp H hb) hx₂
  have hap' : a' ∈ H.perp (H.X t₂.f') := perp_left H (mem_perp_isotropicSpan_of_mem_framePerp' H hb') hx₂'
  have h1 : φ (H.mkW t₁.f ⟨_, hx⟩) = H.mkW t₂.f ⟨a + b, hx₂⟩ :=
    hyeq2.trans (congrArg _ (Subtype.ext hab.symm))
  have h1' : φ' (H.mkW t₁.f' ⟨_, hx'⟩) = H.mkW t₂.f' ⟨a' + b', hx₂'⟩ :=
    hyeq'.trans (congrArg _ (Subtype.ext hab'.symm))
  obtain ⟨hbψ, hφ⟩ := RGHyp.trF H D (hMMU t₁ u.2) hu w hx ha hb hap hx₂ h1
  obtain ⟨hb'ψ, hφ'⟩ := RGHyp.trF' H D (hMMU t₁ u'.2) hu' w' hx' ha' hb' hap' hx₂' h1'
  obtain ⟨hda, hdb⟩ := dec_diff D.hU₂ c ha ha' ha'' hb hb' hb'' hab hab' hab'' hz
  have hb''ψ : b'' = ψ w'' := by
    apply smul_cancel_q g
    rw [← hdb, hbψ, hb'ψ, hψw']
    abel
  have haM : a ∈ MMsharp H t₂ := part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha hb (by rw [hab]; exact hyL)
  have ha'M : a' ∈ MMsharp H t₂ := part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha' hb' (by rw [hab']; exact hy'L)
  have ha''M : a'' ∈ MMsharp H t₂ := part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha'' hb'' (by rw [hab'']; exact hzL)
  refine ⟨⟨a, haM⟩, ⟨a', ha'M⟩, ⟨a'', ha''M⟩, hap, hap', hda, ?_⟩
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext hφ hφ'))
  · exact (D.hθ u ⟨a, haM⟩).mpr ⟨w, hw, by rw [← hbψ, hab]; exact hyL⟩
  · exact (D.hθ u'' ⟨a'', ha''M⟩).mpr ⟨w'', hw'', by rw [← hb''ψ, hab'']; exact hzL⟩

end RG4

end Formalism.L2.SG.LsDatumA
