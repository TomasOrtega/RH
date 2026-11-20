import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsClassSystem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChangeOfSplittingPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlNeOfSplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AnticyclotomicTwistRamifiedPlacesSplitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitSetInertiaPowerTrivialStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DeltaGood

/- English proof (translation)
Rewrite using `[Nat.coprime_comm, hq.coprime_iff_not_dvd]`. Introduce `hd`. Use `Nat.le_of_dvd (by norm_num) hd` as an intermediate fact. Establish `h1 : q = 1` using `by omega`. Conclude with `hq.one_lt.ne' h1`.
-/
theorem coprime_fifteen_of_prime_mod_fifteen_eq_one {q : ℕ} (hq : q.Prime) (hm : q % 15 = 1) : Nat.Coprime 15 q := by
  rw [Nat.coprime_comm, hq.coprime_iff_not_dvd]
  intro hd
  have := Nat.le_of_dvd (by norm_num) hd
  have h1 : q = 1 := by omega
  exact hq.one_lt.ne' h1

/- English proof (translation)
Introduce `D a ha i ch hch f _ b`. Use `set ψ := Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) with hψ`. Establish `hval : ∀ σ, ψ σ = 1 ↔ D.ntw.delta i σ = 1` using `fun σ => by`. Apply the tactic sequence `cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt]`. Establish `hopen : IsOpen (ψ.ker : Set (G D.host.E D.nd.Om))`.

Establish `: ψ.ker = (D.ntw.delta i).ker` using `by ext σ; simp only [MonoidHom.mem_ker]; exact hval σ`. Rewrite using `[this]`. Conclude with `D.ntw.delta_open i`. Establish `hanti : AntiHom D.ntw.cc ψ` using `fun g g' h => by`. Apply the tactic sequence `cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, D.ntw.delta_anti i g g' h]`.

Use `set p := if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde with hp`. Establish `hpp : p.Prime ∧ p % 15 = 1`. Rewrite using `[hp]`. Use `split_ifs`. Conclude with `⟨D.host.pde'_prime, D.host.pde_mod.2⟩`.

Conclude with `⟨D.host.pde_prime, D.host.pde_mod.1⟩`. Establish `hmem : ∀ v : Pl D.host.E, v ∈ D.ntw.pD i ↔ ((p : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal` using `fun v => by`. Use `D.ntw.pD_eq i` as an intermediate fact. Rewrite `this` using `[Set.ext_iff]`. Conclude with `this v`.

Establish `h15 : ∀ P ∈ D.ntw.pD i, ((15 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal`. Introduce `P hP h`. Establish `hpP` using `(hmem P).1 hP`. Establish `hcop : Nat.Coprime 15 p` using `coprime_fifteen_of_prime_mod_fifteen_eq_one hpp.1 hpp.2`. Take `⟨u, w, huw⟩` from `Nat.isCoprime_iff_coprime.2 hcop`.

Apply `P.isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `: ((u * (15 : ℕ) + w * (p : ℕ) : ℤ) : 𝓞 D.host.E) = 1` using `by rw [huw]; simp`. Rewrite using `[← this]`. Use `push_cast`.

Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ (by exact_mod_cast h)) (Ideal.mul_mem_left _ _ (by exact_mod_cast hpP))`. Establish `hconj : ∀ P ∈ D.ntw.pD i, ∀ P', Formalism.BasicNotions.IsConjPl D.host P P' → P' ∈ D.ntw.pD i`. Introduce `P hP P' hc`. Rewrite `hP`, the goal using `[hmem]`. Conclude with `(hc _ _ (by simp)).1 hP`.

Use `set Q := half ch (D.ntw.pD i) with hQ`. Establish `hsplit : SplitSet Q`. Use `GlobalTheory.UnivGood.splitSet_of_split (fun P hP => GlobalTheory.T.anticyclotomicTwist_ramified_places_split D i P (mem_half.1 hP).1) fun P hP P' hP' hc => ?_` and prove the remaining obligations. Establish `hne : P ≠ P'` using `ne_of_split (GlobalTheory.T.anticyclotomicTwist_ramified_places_split D i P (mem_half.1 hP).1) hc`. Conclude with `(hch.pair P P' hc hne).1 (mem_half.1 hP).2 (mem_half.1 hP').2`.

Set `g : (D.ntw.O0 i)ˣ →* Circle` to `unitPart.comp (Units.map f.toMonoidHom)`. Establish `hkey : charOf a f ψ = a.pull (g.comp ψ)`. Rewrite using `[Recip.pull_comp _ hopen]`. Both sides reduce to the same expression. Use `show (⟨Q, charOf a f ψ, resOf (charOf a f ψ)⟩ : Twist D Circle).Good`.

Rewrite using `[hkey]`. Use `GlobalTheory.T.split_set_inertia_power_trivial D D.nd D.ntw a ha Circle (g.comp ψ) ?_ ?_ Q hsplit ?_ ?_` and prove the remaining obligations. Conclude with `Subgroup.isOpen_mono (H₁ := ψ.ker) (fun x hx => by`. Rewrite `hx`, the goal using `[MonoidHom.mem_ker]`. Rewrite using `[MonoidHom.comp_apply, hx, map_one]) hopen`.

Introduce `x x' hx show g (ψ x') = (g (ψ x))⁻¹`. Rewrite using `[hanti x x' hx, map_inv]`. Introduce `P hP`. Establish `hPD` using `(mem_half.1 hP).1`. Use `⟨15, h15 P hPD, fun B hB σ hσ => ?_⟩` and prove the remaining obligations.

Establish `hc` using `D.ntw.delta_15 i P hPD B hB`. Establish `h1 : D.ntw.delta i σ ^ 15 = 1`. Use `pow_card_eq_one' (G := ((Ine (F := D.host.E) B).map (D.ntw.delta i))) (x := ⟨D.ntw.delta i σ, Subgroup.mem_map_of_mem _ hσ⟩)` as an intermediate fact. Rewrite `this` using `[hc]`. Conclude with `congrArg Subtype.val this`.

Establish `h2 : ψ σ ^ 15 = 1`. Apply the tactic sequence `cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, h1]`. Rewrite using `[MonoidHom.comp_apply, ← map_pow, h2, map_one]`. Introduce `v hv hnc B hB σ hσ`. Establish `hvD : v ∉ D.ntw.pD i`.

Introduce `hvD`. Distinguish the cases in `hc : v ∈ ch`. Conclude with `hv (mem_half.2 ⟨hvD, hc⟩)`. Take `⟨v', hv'⟩` from `GlobalTheory.TwistDet.exists_isConjPl v`. Establish `hv'D` using `hconj v hvD v' hv'`.

Establish `hne` using `ne_of_split (GlobalTheory.T.anticyclotomicTwist_ramified_places_split D i v hvD) hv'`. Establish `hv'c : v' ∈ ch`. Assume the negation of the conclusion as `h`. Conclude with `hc (((hch.pair v v' hv' hne).2 h))`. Conclude with `hnc v' (mem_half.2 ⟨hv'D, hv'c⟩) (GlobalTheory.TwistDet.isConjPl_symm hv')`.

Establish `h1 : D.ntw.delta i σ = 1`. Assume the negation of the conclusion as `h`. Conclude with `hvD ((D.ntw.delta_ram i v B hB).1 ⟨σ, hσ, h⟩)`. Rewrite using `[MonoidHom.comp_apply, (hval σ).2 h1, map_one]`.
-/
theorem twistOf_delta_good : ∀ (D : D7) (a : Recip D D.nd.Om), a.Good → ∀ (i : D.ntw.Tw) (ch : Set (Pl D.host.E)), IsChoice ch → ∀ (f : D.ntw.O0 i →+* ℂ), Function.Injective f → ∀ b : Bool, (twistOf a f ch (D.ntw.pD i) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))).Good := by
  intro D a ha i ch hch f _ b
  classical
  set ψ := Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) with hψ
  have hval : ∀ σ, ψ σ = 1 ↔ D.ntw.delta i σ = 1 := fun σ => by
    cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt]
  have hopen : IsOpen (ψ.ker : Set (G D.host.E D.nd.Om)) := by
    have : ψ.ker = (D.ntw.delta i).ker := by ext σ; simp only [MonoidHom.mem_ker]; exact hval σ
    rw [this]; exact D.ntw.delta_open i
  have hanti : AntiHom D.ntw.cc ψ := fun g g' h => by
    cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, D.ntw.delta_anti i g g' h]

  set p := if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde with hp
  have hpp : p.Prime ∧ p % 15 = 1 := by
    rw [hp]; split_ifs
    · exact ⟨D.host.pde'_prime, D.host.pde_mod.2⟩
    · exact ⟨D.host.pde_prime, D.host.pde_mod.1⟩
  have hmem : ∀ v : Pl D.host.E, v ∈ D.ntw.pD i ↔ ((p : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal := fun v => by
    have := D.ntw.pD_eq i
    rw [Set.ext_iff] at this
    exact this v
  have h15 : ∀ P ∈ D.ntw.pD i, ((15 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro P hP h
    have hpP := (hmem P).1 hP
    have hcop : Nat.Coprime 15 p := coprime_fifteen_of_prime_mod_fifteen_eq_one hpp.1 hpp.2
    obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.2 hcop
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have : ((u * (15 : ℕ) + w * (p : ℕ) : ℤ) : 𝓞 D.host.E) = 1 := by rw [huw]; simp
    rw [← this]
    push_cast
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (by exact_mod_cast h)) (Ideal.mul_mem_left _ _ (by exact_mod_cast hpP))
  have hconj : ∀ P ∈ D.ntw.pD i, ∀ P', Formalism.BasicNotions.IsConjPl D.host P P' → P' ∈ D.ntw.pD i := by
    intro P hP P' hc
    rw [hmem] at hP ⊢
    exact (hc _ _ (by simp)).1 hP
  set Q := half ch (D.ntw.pD i) with hQ
  have hsplit : SplitSet Q := by
    refine GlobalTheory.UnivGood.splitSet_of_split (fun P hP => GlobalTheory.T.anticyclotomicTwist_ramified_places_split D i P (mem_half.1 hP).1) fun P hP P' hP' hc => ?_
    have hne : P ≠ P' := ne_of_split (GlobalTheory.T.anticyclotomicTwist_ramified_places_split D i P (mem_half.1 hP).1) hc
    exact (hch.pair P P' hc hne).1 (mem_half.1 hP).2 (mem_half.1 hP').2
  let g : (D.ntw.O0 i)ˣ →* Circle := unitPart.comp (Units.map f.toMonoidHom)
  have hkey : charOf a f ψ = a.pull (g.comp ψ) := by
    rw [Recip.pull_comp _ hopen]
    rfl
  show (⟨Q, charOf a f ψ, resOf (charOf a f ψ)⟩ : Twist D Circle).Good
  rw [hkey]
  refine GlobalTheory.T.split_set_inertia_power_trivial D D.nd D.ntw a ha Circle (g.comp ψ) ?_ ?_ Q hsplit ?_ ?_
  · exact Subgroup.isOpen_mono (H₁ := ψ.ker) (fun x hx => by
      rw [MonoidHom.mem_ker] at hx ⊢
      rw [MonoidHom.comp_apply, hx, map_one]) hopen
  · intro x x' hx
    show g (ψ x') = (g (ψ x))⁻¹
    rw [hanti x x' hx, map_inv]
  · intro P hP
    have hPD := (mem_half.1 hP).1
    refine ⟨15, h15 P hPD, fun B hB σ hσ => ?_⟩
    have hc := D.ntw.delta_15 i P hPD B hB
    have h1 : D.ntw.delta i σ ^ 15 = 1 := by
      have := pow_card_eq_one' (G := ((Ine (F := D.host.E) B).map (D.ntw.delta i)))
        (x := ⟨D.ntw.delta i σ, Subgroup.mem_map_of_mem _ hσ⟩)
      rw [hc] at this
      exact congrArg Subtype.val this
    have h2 : ψ σ ^ 15 = 1 := by
      cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, h1]
    rw [MonoidHom.comp_apply, ← map_pow, h2, map_one]
  · intro v hv hnc B hB σ hσ
    have hvD : v ∉ D.ntw.pD i := by
      intro hvD
      by_cases hc : v ∈ ch
      · exact hv (mem_half.2 ⟨hvD, hc⟩)
      · obtain ⟨v', hv'⟩ := GlobalTheory.TwistDet.exists_isConjPl v
        have hv'D := hconj v hvD v' hv'
        have hne := ne_of_split (GlobalTheory.T.anticyclotomicTwist_ramified_places_split D i v hvD) hv'
        have hv'c : v' ∈ ch := by
          by_contra h
          exact hc (((hch.pair v v' hv' hne).2 h))
        exact hnc v' (mem_half.2 ⟨hv'D, hv'c⟩) (GlobalTheory.TwistDet.isConjPl_symm hv')
    have h1 : D.ntw.delta i σ = 1 := by
      by_contra h
      exact hvD ((D.ntw.delta_ram i v B hB).1 ⟨σ, hσ, h⟩)
    rw [MonoidHom.comp_apply, (hval σ).2 h1, map_one]

end GlobalTheory.DeltaGood

end
