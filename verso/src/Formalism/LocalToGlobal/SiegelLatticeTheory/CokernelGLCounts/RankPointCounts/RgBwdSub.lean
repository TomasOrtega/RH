import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RGHyp

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG6

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

/- English proof (translation)
Introduce and unpack `_ ⟨⟨y', y⟩, ⟨x₁', x₁, hx₁'L, hx₁L, hd₁, hpe⟩, rfl⟩`. Simplify using `only [Prod.mk.injEq] at hpe`. Take `⟨rfl, rfl⟩` from `hpe`. Establish `hcO : algebraMap F E (g.q : F) ∈ M.L.O`. Rewrite using `[M.L.O_def]`.

Use `isIntegral_algebraMap (R := ↥𝒪[F]) (A := E) (x := g.q)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[IsScalarTower.algebraMap_apply (↥𝒪[F]) F E]`. Both sides reduce to the same expression. Use `set c := algebraMap F E (g.q : F) with hc`.

Establish `hcx : ∀ x ∈ Λ₂, c • x ∈ Λ₂` using `fun x hx => Λ₂.smul_mem (⟨c, hcO⟩ : M.L.O) hx`. Take `⟨l, hl, hle⟩` from `exists_of_mem_smulLat H hd₁`. Take `⟨a, ha, b, hb, hab⟩` from `dec_of D.hU₁ (x₁ : V)`. Take `⟨a', ha', b', hb', hab'⟩` from `dec_of D.hU₁ (x₁' : V)`. Take `⟨a'', ha'', b'', hb'', hab''⟩` from `dec_of D.hU₁ l`.

Take `⟨hda, hdb⟩` from `dec_diff D.hU₁ c ha ha' ha'' hb hb' hb'' hab hab' hab'' hle`. Establish `hap : a ∈ H.perp (H.X t₁.f)`. Establish `: a = (x₁ : V) - b` using `by rw [← hab]; abel`. Rewrite using `[this]`. Conclude with `(H.perp _).sub_mem x₁.2 (mem_perp_isotropicSpan_of_mem_framePerp H hb)`.

Establish `hap' : a' ∈ H.perp (H.X t₁.f')`. Establish `: a' = (x₁' : V) - b'` using `by rw [← hab']; abel`. Rewrite using `[this]`. Conclude with `(H.perp _).sub_mem x₁'.2 (mem_perp_isotropicSpan_of_mem_framePerp' H hb')`. Establish `haS : a ∈ MMsharp H t₁` using `part_MMsharp H t₁ t₁.abelian₂ D.hsd₁ D.hMM₁ ha hb (by rw [hab]; exact hx₁L)`.

Establish `haS' : a' ∈ MMsharp H t₁` using `part_MMsharp H t₁ t₁.abelian₂ D.hsd₁ D.hMM₁ ha' hb' (by rw [hab']; exact hx₁'L)`. Establish `haS'' : a'' ∈ MMsharp H t₁` using `part_MMsharp H t₁ t₁.abelian₂ D.hsd₁ D.hMM₁ ha'' hb'' (by rw [hab'']; exact hl)`. Establish `hmemG : (θ (ddMk H t₁ ⟨a, haS⟩), θ (ddMk H t₁ ⟨a'', haS''⟩), φ (H.mkW t₁.f ⟨a, hap⟩), φ' (H.mkW t₁.f' ⟨a', hap'⟩)) ∈ GamR H t₂ c`. Rewrite using `[← hG]`. Conclude with `⟨_, ⟨⟨a, haS⟩, ⟨a', haS'⟩, ⟨a'', haS''⟩, hap, hap', hda, rfl⟩, rfl⟩`.

Take `⟨u, u', u'', hu, hu', huu, hpe2⟩` from `hmemG`. Simplify using `only [Prod.mk.injEq] at hpe2`. Take `⟨e1, e2, e3, e4⟩` from `hpe2`. Establish `key : ∀ (m : MMsharp H t₁) (n : MMsharp H t₂) (v : H.W0 t₁.f t₁.f'), θ (ddMk H t₁ m) = ddMk H t₂ n → (m : V) + v ∈ t₁.abelian₂ → (n : V) + ↑(ψ v) ∈ Λ₂`. Introduce `m n v hmn hv`.

Take `⟨w, hw1, hw2⟩` from `(D.hθ m n).1 hmn`. Establish `h1 : ((v - w : H.W0 t₁.f t₁.f') : V) ∈ t₁.abelian₂`. Establish `: ((v - w : H.W0 t₁.f t₁.f') : V) = ((m : V) + v) - ((m : V) + w)`. Rewrite using `[Submodule.coe_sub]`. Normalize the expressions using the abelian group laws.

Rewrite using `[this]`. Conclude with `t₁.abelian₂.sub_mem hv hw1`. Establish `h2` using `(D.hth (v - w)).1 h1`. Establish `: (n : V) + ↑(ψ v) = ((n : V) + ↑(ψ w)) + ↑(ψ (v - w))`. Rewrite using `[map_sub, Submodule.coe_sub]`.

Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `Λ₂.add_mem hw2 h2`. Establish `hx₂ : (u : V) + ↑(ψ ⟨b, hb⟩) ∈ Λ₂` using `key ⟨a, haS⟩ u ⟨b, hb⟩ e1 (by show a + b ∈ _`. Rewrite using `[hab]`.

Conclude with `hx₁L)`. Establish `hx₂'' : (u'' : V) + ↑(ψ ⟨b'', hb''⟩) ∈ Λ₂` using `key ⟨a'', haS''⟩ u'' ⟨b'', hb''⟩ e2 (by show a'' + b'' ∈ _`. Rewrite using `[hab'']`. Conclude with `hl)`. Establish `hbb : (⟨b', hb'⟩ : H.W0 t₁.f t₁.f') = ⟨b, hb⟩ - c • ⟨b'', hb''⟩` using `Subtype.ext (by show b' = b - c • b''`.

Rewrite using `[← hdb]`. Use the proof step `abel)`. Establish `hx₂' : (u' : V) + ↑(ψ ⟨b', hb'⟩) ∈ Λ₂`. Establish `e : (u' : V) + ↑(ψ ⟨b', hb'⟩) = ((u : V) + ↑(ψ ⟨b, hb⟩)) - c • ((u'' : V) + ↑(ψ ⟨b'', hb''⟩))`. Rewrite using `[hbb, map_sub, map_smul, Submodule.coe_sub, Submodule.coe_smul, smul_add, ← huu]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `Λ₂.sub_mem hx₂ (hcx _ hx₂'')`. Establish `hp₂ : (u : V) + ↑(ψ ⟨b, hb⟩) ∈ H.perp (H.X t₂.f)` using `(H.perp _).add_mem hu (mem_perp_isotropicSpan_of_mem_framePerp H (ψ _).2)`. Establish `hp₂' : (u' : V) + ↑(ψ ⟨b', hb'⟩) ∈ H.perp (H.X t₂.f')` using `(H.perp _).add_mem hu' (mem_perp_isotropicSpan_of_mem_framePerp' H (ψ _).2)`.

Establish `hd₂ : ((u : V) + ↑(ψ ⟨b, hb⟩)) - ((u' : V) + ↑(ψ ⟨b', hb'⟩)) ∈ H.smulLat c Λ₂`. Establish `e : ((u : V) + ↑(ψ ⟨b, hb⟩)) - ((u' : V) + ↑(ψ ⟨b', hb'⟩)) = c • ((u'' : V) + ↑(ψ ⟨b'', hb''⟩))`. Rewrite using `[hbb, map_sub, map_smul, Submodule.coe_sub, Submodule.coe_smul, smul_add, ← huu]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`.

Conclude with `Submodule.subset_span ⟨_, hx₂'', rfl⟩`. Establish `hy : a + b ∈ H.perp (H.X t₁.f)`. Rewrite using `[hab]`. Conclude with `x₁.2`. Establish `hy' : a' + b' ∈ H.perp (H.X t₁.f')`.

Rewrite using `[hab']`. Conclude with `x₁'.2`. Establish `hC : φ (H.mkW t₁.f ⟨b, mem_perp_isotropicSpan_of_mem_framePerp H hb⟩) = H.mkW t₂.f ⟨↑(ψ ⟨b, hb⟩), mem_perp_isotropicSpan_of_mem_framePerp H (ψ _).2⟩` using `D.hC1 ⟨b, hb⟩`. Establish `hC' : φ' (H.mkW t₁.f' ⟨b', mem_perp_isotropicSpan_of_mem_framePerp' H hb'⟩) = H.mkW t₂.f' ⟨↑(ψ ⟨b', hb'⟩), mem_perp_isotropicSpan_of_mem_framePerp' H (ψ _).2⟩` using `D.hC1' ⟨b', hb'⟩`. Establish `hφ : φ (H.mkW t₁.f x₁) = H.mkW t₂.f ⟨_, hp₂⟩`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mkW_add H a b hap (mem_perp_isotropicSpan_of_mem_framePerp H hb), map_add, e3, hC]`. Use `_ = H.mkW t₂.f ⟨_, hp₂⟩ := (mkW_add H _ _ hu _).symm`. Establish `hφ' : φ' (H.mkW t₁.f' x₁') = H.mkW t₂.f' ⟨_, hp₂'⟩`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mkW_add H a' b' hap' (mem_perp_isotropicSpan_of_mem_framePerp' H hb'), map_add, e4, hC']`. Use `_ = H.mkW t₂.f' ⟨_, hp₂'⟩ := (mkW_add H _ _ hu' _).symm`. Conclude with `⟨⟨_, hp₂'⟩, ⟨_, hp₂⟩, hx₂', hx₂, hd₂, Prod.ext hφ' hφ⟩`.
-/
theorem rg_bwd_sub (g : SplitG M.L) {t₁ t₂ : Term V M r} {Λ₂ : Submodule M.L.O V}
    {ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f')} {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂}
    {φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'} (D : RGHyp H t₁ t₂ Λ₂ ψ θ φ φ')
    (hG : (fun p => (θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2)) '' GamR H t₁ (algebraMap F E (g.q : F)) =
      GamR H t₂ (algebraMap F E (g.q : F))) :
    Prod.map φ' φ '' H.iotaGraph g t₁ ⊆ H.iotaGraph g ⟨Λ₂, t₂.f, t₂.f', t₂.T, t₂.T'⟩ := by
  rintro _ ⟨⟨y', y⟩, ⟨x₁', x₁, hx₁'L, hx₁L, hd₁, hpe⟩, rfl⟩
  simp only [Prod.mk.injEq] at hpe
  obtain ⟨rfl, rfl⟩ := hpe
  have hcO : algebraMap F E (g.q : F) ∈ M.L.O := by
    rw [M.L.O_def]
    have := isIntegral_algebraMap (R := ↥𝒪[F]) (A := E) (x := g.q)
    convert this using 1
    rw [IsScalarTower.algebraMap_apply (↥𝒪[F]) F E]
    rfl
  set c := algebraMap F E (g.q : F) with hc
  have hcx : ∀ x ∈ Λ₂, c • x ∈ Λ₂ := fun x hx => Λ₂.smul_mem (⟨c, hcO⟩ : M.L.O) hx
  obtain ⟨l, hl, hle⟩ := exists_of_mem_smulLat H hd₁
  obtain ⟨a, ha, b, hb, hab⟩ := dec_of D.hU₁ (x₁ : V)
  obtain ⟨a', ha', b', hb', hab'⟩ := dec_of D.hU₁ (x₁' : V)
  obtain ⟨a'', ha'', b'', hb'', hab''⟩ := dec_of D.hU₁ l
  obtain ⟨hda, hdb⟩ := dec_diff D.hU₁ c ha ha' ha'' hb hb' hb'' hab hab' hab'' hle
  have hap : a ∈ H.perp (H.X t₁.f) := by
    have : a = (x₁ : V) - b := by rw [← hab]; abel
    rw [this]
    exact (H.perp _).sub_mem x₁.2 (mem_perp_isotropicSpan_of_mem_framePerp H hb)
  have hap' : a' ∈ H.perp (H.X t₁.f') := by
    have : a' = (x₁' : V) - b' := by rw [← hab']; abel
    rw [this]
    exact (H.perp _).sub_mem x₁'.2 (mem_perp_isotropicSpan_of_mem_framePerp' H hb')
  have haS : a ∈ MMsharp H t₁ :=
    part_MMsharp H t₁ t₁.abelian₂ D.hsd₁ D.hMM₁ ha hb (by rw [hab]; exact hx₁L)
  have haS' : a' ∈ MMsharp H t₁ :=
    part_MMsharp H t₁ t₁.abelian₂ D.hsd₁ D.hMM₁ ha' hb' (by rw [hab']; exact hx₁'L)
  have haS'' : a'' ∈ MMsharp H t₁ :=
    part_MMsharp H t₁ t₁.abelian₂ D.hsd₁ D.hMM₁ ha'' hb'' (by rw [hab'']; exact hl)
  have hmemG : (θ (ddMk H t₁ ⟨a, haS⟩), θ (ddMk H t₁ ⟨a'', haS''⟩), φ (H.mkW t₁.f ⟨a, hap⟩),
      φ' (H.mkW t₁.f' ⟨a', hap'⟩)) ∈ GamR H t₂ c := by
    rw [← hG]
    exact ⟨_, ⟨⟨a, haS⟩, ⟨a', haS'⟩, ⟨a'', haS''⟩, hap, hap', hda, rfl⟩, rfl⟩
  obtain ⟨u, u', u'', hu, hu', huu, hpe2⟩ := hmemG
  simp only [Prod.mk.injEq] at hpe2
  obtain ⟨e1, e2, e3, e4⟩ := hpe2
  have key : ∀ (m : MMsharp H t₁) (n : MMsharp H t₂) (v : H.W0 t₁.f t₁.f'),
      θ (ddMk H t₁ m) = ddMk H t₂ n → (m : V) + v ∈ t₁.abelian₂ → (n : V) + ↑(ψ v) ∈ Λ₂ := by
    intro m n v hmn hv
    obtain ⟨w, hw1, hw2⟩ := (D.hθ m n).1 hmn
    have h1 : ((v - w : H.W0 t₁.f t₁.f') : V) ∈ t₁.abelian₂ := by
      have : ((v - w : H.W0 t₁.f t₁.f') : V) = ((m : V) + v) - ((m : V) + w) := by
        rw [Submodule.coe_sub]
        abel
      rw [this]
      exact t₁.abelian₂.sub_mem hv hw1
    have h2 := (D.hth (v - w)).1 h1
    have : (n : V) + ↑(ψ v) = ((n : V) + ↑(ψ w)) + ↑(ψ (v - w)) := by
      rw [map_sub, Submodule.coe_sub]
      abel
    rw [this]
    exact Λ₂.add_mem hw2 h2
  have hx₂ : (u : V) + ↑(ψ ⟨b, hb⟩) ∈ Λ₂ :=
    key ⟨a, haS⟩ u ⟨b, hb⟩ e1 (by
      show a + b ∈ _
      rw [hab]
      exact hx₁L)
  have hx₂'' : (u'' : V) + ↑(ψ ⟨b'', hb''⟩) ∈ Λ₂ :=
    key ⟨a'', haS''⟩ u'' ⟨b'', hb''⟩ e2 (by
      show a'' + b'' ∈ _
      rw [hab'']
      exact hl)
  have hbb : (⟨b', hb'⟩ : H.W0 t₁.f t₁.f') = ⟨b, hb⟩ - c • ⟨b'', hb''⟩ :=
    Subtype.ext (by
      show b' = b - c • b''
      rw [← hdb]
      abel)
  have hx₂' : (u' : V) + ↑(ψ ⟨b', hb'⟩) ∈ Λ₂ := by
    have e : (u' : V) + ↑(ψ ⟨b', hb'⟩) =
        ((u : V) + ↑(ψ ⟨b, hb⟩)) - c • ((u'' : V) + ↑(ψ ⟨b'', hb''⟩)) := by
      rw [hbb, map_sub, map_smul, Submodule.coe_sub, Submodule.coe_smul, smul_add, ← huu]
      abel
    rw [e]
    exact Λ₂.sub_mem hx₂ (hcx _ hx₂'')
  have hp₂ : (u : V) + ↑(ψ ⟨b, hb⟩) ∈ H.perp (H.X t₂.f) :=
    (H.perp _).add_mem hu (mem_perp_isotropicSpan_of_mem_framePerp H (ψ _).2)
  have hp₂' : (u' : V) + ↑(ψ ⟨b', hb'⟩) ∈ H.perp (H.X t₂.f') :=
    (H.perp _).add_mem hu' (mem_perp_isotropicSpan_of_mem_framePerp' H (ψ _).2)
  have hd₂ : ((u : V) + ↑(ψ ⟨b, hb⟩)) - ((u' : V) + ↑(ψ ⟨b', hb'⟩)) ∈ H.smulLat c Λ₂ := by
    have e : ((u : V) + ↑(ψ ⟨b, hb⟩)) - ((u' : V) + ↑(ψ ⟨b', hb'⟩)) =
        c • ((u'' : V) + ↑(ψ ⟨b'', hb''⟩)) := by
      rw [hbb, map_sub, map_smul, Submodule.coe_sub, Submodule.coe_smul, smul_add, ← huu]
      abel
    rw [e]
    exact Submodule.subset_span ⟨_, hx₂'', rfl⟩
  have hy : a + b ∈ H.perp (H.X t₁.f) := by
    rw [hab]
    exact x₁.2
  have hy' : a' + b' ∈ H.perp (H.X t₁.f') := by
    rw [hab']
    exact x₁'.2
  have hC : φ (H.mkW t₁.f ⟨b, mem_perp_isotropicSpan_of_mem_framePerp H hb⟩) =
      H.mkW t₂.f ⟨↑(ψ ⟨b, hb⟩), mem_perp_isotropicSpan_of_mem_framePerp H (ψ _).2⟩ := D.hC1 ⟨b, hb⟩
  have hC' : φ' (H.mkW t₁.f' ⟨b', mem_perp_isotropicSpan_of_mem_framePerp' H hb'⟩) =
      H.mkW t₂.f' ⟨↑(ψ ⟨b', hb'⟩), mem_perp_isotropicSpan_of_mem_framePerp' H (ψ _).2⟩ := D.hC1' ⟨b', hb'⟩
  have hφ : φ (H.mkW t₁.f x₁) = H.mkW t₂.f ⟨_, hp₂⟩ := by
    calc φ (H.mkW t₁.f x₁) = φ (H.mkW t₁.f ⟨a + b, hy⟩) :=
          congrArg φ (mkW_congr H x₁.2 hy hab.symm)
      _ = H.mkW t₂.f ⟨u, hu⟩ + H.mkW t₂.f ⟨↑(ψ ⟨b, hb⟩), mem_perp_isotropicSpan_of_mem_framePerp H (ψ _).2⟩ := by
          rw [mkW_add H a b hap (mem_perp_isotropicSpan_of_mem_framePerp H hb), map_add, e3, hC]
      _ = H.mkW t₂.f ⟨_, hp₂⟩ := (mkW_add H _ _ hu _).symm
  have hφ' : φ' (H.mkW t₁.f' x₁') = H.mkW t₂.f' ⟨_, hp₂'⟩ := by
    calc φ' (H.mkW t₁.f' x₁') = φ' (H.mkW t₁.f' ⟨a' + b', hy'⟩) :=
          congrArg φ' (mkW_congr H x₁'.2 hy' hab'.symm)
      _ = H.mkW t₂.f' ⟨u', hu'⟩ + H.mkW t₂.f' ⟨↑(ψ ⟨b', hb'⟩), mem_perp_isotropicSpan_of_mem_framePerp' H (ψ _).2⟩ := by
          rw [mkW_add H a' b' hap' (mem_perp_isotropicSpan_of_mem_framePerp' H hb'), map_add, e4, hC']
      _ = H.mkW t₂.f' ⟨_, hp₂'⟩ := (mkW_add H _ _ hu' _).symm
  exact ⟨⟨_, hp₂'⟩, ⟨_, hp₂⟩, hx₂', hx₂, hd₂, Prod.ext hφ' hφ⟩

end RG6

end Formalism.L2.SG.LsDatumA
