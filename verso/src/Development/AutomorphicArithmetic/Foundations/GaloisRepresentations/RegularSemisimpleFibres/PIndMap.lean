import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.SuppBCOfMix
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1600000 in
/- English proof (translation)
Introduce `hSupp hPara k _ _ _ _ N s d hd W Z _ _ _ _ ρ κ j hj hjκ`. Use `set e := stdBlocks d hd with he`. Set `σ` to `(twist ρ (deltaHalf k fun a : Fin s => Fin (d a))).comp (leviProj k e)`. Establish `hσ : ∀ (p : parab k e), leviProj k e p ∈ leviK k (fun a : Fin s => Fin (d a)) → ∀ w : W, σ p w = ρ (leviProj k e p) w`. Introduce `p hK w`.

Establish `h3` using `deltaHalf_of_mem_leviK hK`. Simplify using `only [σ, MonoidHom.comp_apply, twist, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply, h3, Units.val_one, one_smul]`. Establish `key : ∀ z : Z, ∀ p : parab k e, (p : GL (Fin N) k) ∈ KOne k (Fin N) → σ p (j z) = j z`. Introduce `z p hp`. Establish `hl` using `(hPara k e).2 p hp`.

Establish `hK : leviProj k e p ∈ leviK k (fun a : Fin s => Fin (d a))`. Rewrite using `[leviK, Subgroup.mem_pi]`. Rewrite `hl` using `[leviKOne, Subgroup.mem_pi]`. Introduce `a ha`. Conclude with `GlobalTheory.StepData.KOne_le_KO (hl a ha)`.

Establish `h1` using `(redLevi_eq_one_iff ⟨_, hK⟩).2 hl`. Establish `h2` using `hjκ ⟨_, hK⟩ z`. Rewrite `h2` using `[h1, map_one]`. Rewrite using `[hσ p hK]`. Conclude with `h2.symm`.

Use `choose F hF1 hF0 using fun z => hSupp (GL (Fin N) k) W (parab k e) (KOne k (Fin N)) σ (j z) GlobalTheory.StepData.isOpen_KOne (key z)`. Establish `uniq : ∀ (u : W) (f f' : GL (Fin N) k → W), (∀ (p : parab k e), ∀ c ∈ KOne k (Fin N), f ((p : GL (Fin N) k) * c) = σ p u) → (∀ g, (¬∃ (p : parab k e), ∃ c ∈ KOne k (Fin N), g = (p : GL (Fin N) k) * c) → f g = 0) → (∀ (p : parab k e), ∀ c ∈ KOne k (Fin N), f' ((p : GL (Fin N) k) * …`. Introduce `u f f' h1 h0 h1' h0'`. Use function extensionality and compare the values at `g`. Distinguish the cases in `hg : ∃ (p : parab k e), ∃ c ∈ KOne k (Fin N), g = (p : GL (Fin N) k) * c`.

Take `⟨p, c, hc, rfl⟩` from `hg`. Rewrite using `[h1 p c hc, h1' p c hc]`. Rewrite using `[h0 g hg, h0' g hg]`. Establish `hfix : ∀ z, F z ∈ fixed (parInd e ρ) (KOne k (Fin N))`. Introduce `z`.

Rewrite using `[GlobalTheory.Parabolic.mem_fixed]`. Introduce `c hc`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`.

Express the relevant statement in the definitionally equal form `(F z).1.1 (g * c) = (F z).1.1 g`. Distinguish the cases in `hg : ∃ (p : parab k e), ∃ c' ∈ KOne k (Fin N), g = (p : GL (Fin N) k) * c'`. Take `⟨p, c', hc', rfl⟩` from `hg`. Rewrite using `[mul_assoc, hF1 z p _ (mul_mem hc' hc), hF1 z p c' hc']`. Rewrite using `[hF0 z g hg, hF0 z (g * c)]`.

Introduce and unpack `⟨p, c', hc', h⟩`. Conclude with `hg ⟨p, c' * c⁻¹, mul_mem hc' (inv_mem hc), by rw [← mul_assoc, ← h, mul_inv_cancel_right]⟩`. Set `Φ : Z →ₗ[ℂ] fixed (parInd e ρ) (KOne k (Fin N))` to `{ toFun := fun z => ⟨F z, hfix z⟩ map_add' := by`. Introduce `z z'`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(F (z + z')).1.1 = (F z).1.1 + (F z').1.1`. Use `uniq (j (z + z')) _ _ (hF1 _) (hF0 _) ?_ ?_` and prove the remaining obligations. Introduce `p c hc`.

Simplify using `only [Pi.add_apply, hF1 z p c hc, hF1 z' p c hc, map_add]`. Introduce `g hg`. Simplify using `only [Pi.add_apply, hF0 z g hg, hF0 z' g hg, add_zero]`. Use the proof step `map_smul' := by`. Introduce `a z`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(F (a • z)).1.1 = a • (F z).1.1`. Use `uniq (j (a • z)) _ _ (hF1 _) (hF0 _) ?_ ?_` and prove the remaining obligations.

Introduce `p c hc`. Simplify using `only [Pi.smul_apply, hF1 z p c hc, map_smul]`. Introduce `g hg`. Simplify using `only [Pi.smul_apply, hF0 z g hg, smul_zero] }`. Set `ev : fixed (parInd e ρ) (KOne k (Fin N)) →ₗ[ℂ] W` to `{ toFun := fun v => v.1.1.1 1 map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`.

Establish `hev : ∀ z, (F z).1.1 1 = j z`. Introduce `z`. Use `hF1 z 1 1 (one_mem _)` as an intermediate fact. Simplify using `using this`. Use `⟨Φ, ev, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `p z`. Take `⟨g, hg⟩` from `redK_surjective (k := k) (n := Fin N) (p : GL (Fin N) 𝓀[k])`. Establish `hgP : (g : GL (Fin N) k) ∈ parahoric k e` using `(coe_mem_levelPre g).2 (by rw [hg]; exact p.2)`. Take `⟨p', x, hp'KO, hpx, hxred, c, hc, hgc⟩` from `(hPara k e).1 ⟨g, hgP⟩`. Establish `hgc' : (g : GL (Fin N) k) = (p' : GL (Fin N) k) * c` using `hgc`.

Establish `hproj : parahoricProj k e ⟨g, hgP⟩ = leviProj 𝓀[k] e p` using `by show leviProj 𝓀[k] _ _ = _`. Conclude with `congrArg _ (Subtype.ext (by exact hg))`. Establish `hz' : j (κ (leviProj 𝓀[k] e p) z) = ρ x (j z)`. Rewrite using `[← hproj, ← hxred]`. Conclude with `hjκ x z`.

Establish `hσp' : σ p' (j z) = j (κ (leviProj 𝓀[k] e p) z)`. Rewrite using `[hz', hσ p' (by rw [hpx]; exact x.2), hpx]`. Establish `hn` using `KO_le_normalizer (k := k) (n := Fin N) hp'KO`. Rewrite using `[← hg]`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[levelZero_apply]`. Express the relevant statement in the definitionally equal form `(F _).1.1 = fun h => (F z).1.1 (h * (g : GL (Fin N) k))`. Use `uniq (j (κ (leviProj 𝓀[k] e p) z)) _ _ (hF1 _) (hF0 _) ?_ ?_` and prove the remaining obligations.

Introduce `q c1 hc1`. Establish `hc2 : (p' : GL (Fin N) k)⁻¹ * c1 * (p' : GL (Fin N) k) * c ∈ KOne k (Fin N)`. Use `mul_mem ?_ hc` and prove the remaining obligations. Use `(Subgroup.mem_normalizer_iff.1 (inv_mem hn) c1).1 hc1` as an intermediate fact. Simplify using `using this`.

Establish `heq : (q : GL (Fin N) k) * c1 * (g : GL (Fin N) k) = ((q * p' : parab k e) : GL (Fin N) k) * ((p' : GL (Fin N) k)⁻¹ * c1 * (p' : GL (Fin N) k) * c)`. Rewrite using `[hgc', Subgroup.coe_mul]`. Use `group`. Use `show (F z).1.1 ((q : GL (Fin N) k) * c1 * (g : GL (Fin N) k)) = _`. Rewrite using `[heq, hF1 z (q * p') _ hc2, map_mul, Module.End.mul_apply, hσp']`.

Introduce `h hh show (F z).1.1 (h * (g : GL (Fin N) k)) = 0`. Apply `hF0` to reduce the goal to its premises. Introduce and unpack `⟨q, c2, hc2, hq⟩`. Apply `hh` to reduce the goal to its premises. Use `⟨q * p'⁻¹, (p' : GL (Fin N) k) * (c2 * c⁻¹) * (p' : GL (Fin N) k)⁻¹, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `(Subgroup.mem_normalizer_iff.1 hn (c2 * c⁻¹)).1 (mul_mem hc2 (inv_mem hc))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hq, hgc', Subgroup.coe_mul, Subgroup.coe_inv]`. Use `group`. Introduce `γ hγ z`.

Take `⟨g, rfl⟩` from `redK_surjective (k := k) (n := Fin N) γ`. Use `show ((levelZero (parInd e ρ) (redK k (Fin N) g)) (Φ z)).1.1.1 1 = 0`. Rewrite using `[levelZero_apply]`. Express the relevant statement in the definitionally equal form `(F z).1.1 (1 * (g : GL (Fin N) k)) = 0`. Rewrite using `[one_mul]`.

Apply `hF0 z` to reduce the goal to its premises. Introduce and unpack `⟨p, c, hc, hpc⟩`. Apply `hγ` to reduce the goal to its premises. Establish `hcKO : c⁻¹ ∈ KO k (Fin N)` using `inv_mem (GlobalTheory.StepData.KOne_le_KO hc)`. Establish `hpKO : (p : GL (Fin N) k) ∈ KO k (Fin N)`.

Establish `: (p : GL (Fin N) k) = g * c⁻¹` using `by rw [hpc, mul_inv_cancel_right]`. Rewrite using `[this]`. Conclude with `mul_mem g.2 hcKO`. Establish `hred : redK k (Fin N) ⟨p, hpKO⟩ = redK k (Fin N) g`. Establish `: (⟨p, hpKO⟩ : KO k (Fin N)) = g * ⟨c⁻¹, hcKO⟩`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show (p : GL (Fin N) k) = g * c⁻¹`. Rewrite using `[hpc, mul_inv_cancel_right]`. Rewrite using `[this, map_mul, (redK_eq_one_iff ⟨c⁻¹, hcKO⟩).2 (inv_mem hc), mul_one]`. Rewrite using `[← hred, mem_parab_iff]`.

Introduce `a b i i' hab`. Rewrite using `[redK_eq_zero_iff]`. Use `(mem_parab_iff.1 p.2) a b i i' hab` as an intermediate fact. Simplify using `[this]`. Introduce `z hz`.

Apply `hj` to reduce the goal to its premises. Rewrite using `[map_zero, ← hev z]`. Conclude with `hz`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.indMap :
    UpperTheory.Gal.TypesAndIwahori.IndSupp → UpperTheory.Gal.TypesAndIwahori.ParaFactor → IndMap := by
  intro hSupp hPara k _ _ _ _ N s d hd W Z _ _ _ _ ρ κ j hj hjκ
  set e := stdBlocks d hd with he
  let σ := (twist ρ (deltaHalf k fun a : Fin s => Fin (d a))).comp (leviProj k e)
  have hσ : ∀ (p : parab k e), leviProj k e p ∈ leviK k (fun a : Fin s => Fin (d a)) →
      ∀ w : W, σ p w = ρ (leviProj k e p) w := by
    intro p hK w
    have h3 := deltaHalf_of_mem_leviK hK
    simp only [σ, MonoidHom.comp_apply, twist, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply, h3,
      Units.val_one, one_smul]
  have key : ∀ z : Z, ∀ p : parab k e, (p : GL (Fin N) k) ∈ KOne k (Fin N) → σ p (j z) = j z := by
    intro z p hp
    have hl := (hPara k e).2 p hp
    have hK : leviProj k e p ∈ leviK k (fun a : Fin s => Fin (d a)) := by
      rw [leviK, Subgroup.mem_pi]
      rw [leviKOne, Subgroup.mem_pi] at hl
      intro a ha
      exact GlobalTheory.StepData.KOne_le_KO (hl a ha)
    have h1 := (redLevi_eq_one_iff ⟨_, hK⟩).2 hl
    have h2 := hjκ ⟨_, hK⟩ z
    rw [h1, map_one] at h2
    rw [hσ p hK]
    exact h2.symm
  choose F hF1 hF0 using fun z => hSupp (GL (Fin N) k) W (parab k e) (KOne k (Fin N)) σ (j z)
    GlobalTheory.StepData.isOpen_KOne (key z)
  have uniq : ∀ (u : W) (f f' : GL (Fin N) k → W),
      (∀ (p : parab k e), ∀ c ∈ KOne k (Fin N), f ((p : GL (Fin N) k) * c) = σ p u) →
      (∀ g, (¬∃ (p : parab k e), ∃ c ∈ KOne k (Fin N), g = (p : GL (Fin N) k) * c) → f g = 0) →
      (∀ (p : parab k e), ∀ c ∈ KOne k (Fin N), f' ((p : GL (Fin N) k) * c) = σ p u) →
      (∀ g, (¬∃ (p : parab k e), ∃ c ∈ KOne k (Fin N), g = (p : GL (Fin N) k) * c) → f' g = 0) →
      f = f' := by
    intro u f f' h1 h0 h1' h0'
    funext g
    by_cases hg : ∃ (p : parab k e), ∃ c ∈ KOne k (Fin N), g = (p : GL (Fin N) k) * c
    · obtain ⟨p, c, hc, rfl⟩ := hg
      rw [h1 p c hc, h1' p c hc]
    · rw [h0 g hg, h0' g hg]
  have hfix : ∀ z, F z ∈ fixed (parInd e ρ) (KOne k (Fin N)) := by
    intro z
    rw [GlobalTheory.Parabolic.mem_fixed]
    intro c hc
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change (F z).1.1 (g * c) = (F z).1.1 g
    by_cases hg : ∃ (p : parab k e), ∃ c' ∈ KOne k (Fin N), g = (p : GL (Fin N) k) * c'
    · obtain ⟨p, c', hc', rfl⟩ := hg
      rw [mul_assoc, hF1 z p _ (mul_mem hc' hc), hF1 z p c' hc']
    · rw [hF0 z g hg, hF0 z (g * c)]
      rintro ⟨p, c', hc', h⟩
      exact hg ⟨p, c' * c⁻¹, mul_mem hc' (inv_mem hc), by rw [← mul_assoc, ← h, mul_inv_cancel_right]⟩
  let Φ : Z →ₗ[ℂ] fixed (parInd e ρ) (KOne k (Fin N)) :=
    { toFun := fun z => ⟨F z, hfix z⟩
      map_add' := by
        intro z z'
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        change (F (z + z')).1.1 = (F z).1.1 + (F z').1.1
        refine uniq (j (z + z')) _ _ (hF1 _) (hF0 _) ?_ ?_
        · intro p c hc
          simp only [Pi.add_apply, hF1 z p c hc, hF1 z' p c hc, map_add]
        · intro g hg
          simp only [Pi.add_apply, hF0 z g hg, hF0 z' g hg, add_zero]
      map_smul' := by
        intro a z
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        change (F (a • z)).1.1 = a • (F z).1.1
        refine uniq (j (a • z)) _ _ (hF1 _) (hF0 _) ?_ ?_
        · intro p c hc
          simp only [Pi.smul_apply, hF1 z p c hc, map_smul]
        · intro g hg
          simp only [Pi.smul_apply, hF0 z g hg, smul_zero] }
  let ev : fixed (parInd e ρ) (KOne k (Fin N)) →ₗ[ℂ] W :=
    { toFun := fun v => v.1.1.1 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : ∀ z, (F z).1.1 1 = j z := by
    intro z
    have := hF1 z 1 1 (one_mem _)
    simpa using this
  refine ⟨Φ, ev, ?_, ?_, ?_⟩
  · intro p z
    obtain ⟨g, hg⟩ := redK_surjective (k := k) (n := Fin N) (p : GL (Fin N) 𝓀[k])
    have hgP : (g : GL (Fin N) k) ∈ parahoric k e := (coe_mem_levelPre g).2 (by rw [hg]; exact p.2)
    obtain ⟨p', x, hp'KO, hpx, hxred, c, hc, hgc⟩ := (hPara k e).1 ⟨g, hgP⟩
    have hgc' : (g : GL (Fin N) k) = (p' : GL (Fin N) k) * c := hgc
    have hproj : parahoricProj k e ⟨g, hgP⟩ = leviProj 𝓀[k] e p := by
      show leviProj 𝓀[k] _ _ = _
      exact congrArg _ (Subtype.ext (by exact hg))
    have hz' : j (κ (leviProj 𝓀[k] e p) z) = ρ x (j z) := by
      rw [← hproj, ← hxred]
      exact hjκ x z
    have hσp' : σ p' (j z) = j (κ (leviProj 𝓀[k] e p) z) := by
      rw [hz', hσ p' (by rw [hpx]; exact x.2), hpx]
    have hn := KO_le_normalizer (k := k) (n := Fin N) hp'KO
    rw [← hg]
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rw [levelZero_apply]
    change (F _).1.1 = fun h => (F z).1.1 (h * (g : GL (Fin N) k))
    refine uniq (j (κ (leviProj 𝓀[k] e p) z)) _ _ (hF1 _) (hF0 _) ?_ ?_
    · intro q c1 hc1
      have hc2 : (p' : GL (Fin N) k)⁻¹ * c1 * (p' : GL (Fin N) k) * c ∈ KOne k (Fin N) := by
        refine mul_mem ?_ hc
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) c1).1 hc1
        simpa using this
      have heq : (q : GL (Fin N) k) * c1 * (g : GL (Fin N) k) =
          ((q * p' : parab k e) : GL (Fin N) k) * ((p' : GL (Fin N) k)⁻¹ * c1 * (p' : GL (Fin N) k) * c) := by
        rw [hgc', Subgroup.coe_mul]
        group
      show (F z).1.1 ((q : GL (Fin N) k) * c1 * (g : GL (Fin N) k)) = _
      rw [heq, hF1 z (q * p') _ hc2, map_mul, Module.End.mul_apply, hσp']
    · intro h hh
      show (F z).1.1 (h * (g : GL (Fin N) k)) = 0
      apply hF0
      rintro ⟨q, c2, hc2, hq⟩
      apply hh
      refine ⟨q * p'⁻¹, (p' : GL (Fin N) k) * (c2 * c⁻¹) * (p' : GL (Fin N) k)⁻¹, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 hn (c2 * c⁻¹)).1 (mul_mem hc2 (inv_mem hc))
      · calc h = (h * (g : GL (Fin N) k)) * (g : GL (Fin N) k)⁻¹ := by group
          _ = _ := by
            rw [hq, hgc', Subgroup.coe_mul, Subgroup.coe_inv]
            group
  · intro γ hγ z
    obtain ⟨g, rfl⟩ := redK_surjective (k := k) (n := Fin N) γ
    show ((levelZero (parInd e ρ) (redK k (Fin N) g)) (Φ z)).1.1.1 1 = 0
    rw [levelZero_apply]
    change (F z).1.1 (1 * (g : GL (Fin N) k)) = 0
    rw [one_mul]
    apply hF0 z
    rintro ⟨p, c, hc, hpc⟩
    apply hγ
    have hcKO : c⁻¹ ∈ KO k (Fin N) := inv_mem (GlobalTheory.StepData.KOne_le_KO hc)
    have hpKO : (p : GL (Fin N) k) ∈ KO k (Fin N) := by
      have : (p : GL (Fin N) k) = g * c⁻¹ := by rw [hpc, mul_inv_cancel_right]
      rw [this]
      exact mul_mem g.2 hcKO
    have hred : redK k (Fin N) ⟨p, hpKO⟩ = redK k (Fin N) g := by
      have : (⟨p, hpKO⟩ : KO k (Fin N)) = g * ⟨c⁻¹, hcKO⟩ := by
        apply Subtype.ext
        show (p : GL (Fin N) k) = g * c⁻¹
        rw [hpc, mul_inv_cancel_right]
      rw [this, map_mul, (redK_eq_one_iff ⟨c⁻¹, hcKO⟩).2 (inv_mem hc), mul_one]
    rw [← hred, mem_parab_iff]
    intro a b i i' hab
    rw [redK_eq_zero_iff]
    have := (mem_parab_iff.1 p.2) a b i i' hab
    simp [this]
  · intro z hz
    apply hj
    rw [map_zero, ← hev z]
    exact hz
