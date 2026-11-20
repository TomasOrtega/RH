import Mathlib

namespace GlobalTheory

open IsLocalization

/- English proof (translation)
Introduce `S _ f₀ q hq hf₀ J _ m hm`. Use `haveI := Fintype.ofFinite J`. Establish `hdisj : Disjoint (↑(Submonoid.powers f₀) : Set S) ↑q` using `(Ideal.disjoint_powers_iff_notMem f₀ hq.isRadical).2 hf₀`. Use `haveI hq' : (Ideal.map (algebraMap S (Localization.Away f₀)) q).IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f₀) (Localization.Away f₀) q hq hdisj`. Use `set d : (Localization.Away f₀) := ∏ i, m i with hd`.

Establish `hdq : d ∉ Ideal.map (algebraMap S (Localization.Away f₀)) q`. Introduce `h`. Take `⟨i, -, hi⟩` from `(Ideal.IsPrime.prod_mem_iff (p := Ideal.map (algebraMap S (Localization.Away f₀)) q)).1 h`. Conclude with `hm i hi`. Take `⟨⟨a, y⟩, hay⟩` from `IsLocalization.mk'_surjective (Submonoid.powers f₀) d`.

Simplify using `only at hay`. Establish `hspec : d * algebraMap S (Localization.Away f₀) y = algebraMap S (Localization.Away f₀) a`. Rewrite using `[← hay]`. Conclude with `IsLocalization.mk'_spec (Localization.Away f₀) a y`. Establish `hyu : IsUnit (algebraMap S (Localization.Away f₀) y)` using `IsLocalization.map_units (Localization.Away f₀) y`.

Establish `ha : a ∉ q`. Introduce `haq`. Establish `h1 : algebraMap S (Localization.Away f₀) a ∈ Ideal.map (algebraMap S (Localization.Away f₀)) q` using `Ideal.mem_map_of_mem _ haq`. Rewrite `h1` using `[← hspec]`. Break down `hq'.mem_or_mem h1 with h2 | h2` into its components or cases.

Conclude with `hdq h2`. Conclude with `hq'.ne_top (Ideal.eq_top_of_isUnit_mem _ h2 hyu)`. Use `⟨f₀ * a, fun h => (hq.mem_or_mem h).elim hf₀ ha, ?_⟩` and prove the remaining obligations. Set `ψ : (Localization.Away f₀) →+* Localization.Away (f₀ * a)` to `IsLocalization.Away.awayToAwayRight f₀ a`. Set `φ : (Localization.Away f₀) →ₐ[S] Localization.Away (f₀ * a)` to `{ ψ with commutes' := fun r => IsLocalization.Away.awayToAwayRight_eq f₀ a r }`.

Use `⟨φ, fun i => ?_⟩` and prove the remaining obligations. Establish `hφ : ∀ x, φ x = ψ x` using `fun _ => rfl`. Establish `hau : IsUnit (algebraMap S (Localization.Away (f₀ * a)) a)`. Establish `hu : IsUnit (algebraMap S (Localization.Away (f₀ * a)) (f₀ * a))` using `IsLocalization.Away.algebraMap_isUnit (f₀ * a)`. Rewrite `hu` using `[map_mul]`.

Conclude with `isUnit_of_mul_isUnit_right hu`. Establish `hyu' : IsUnit (φ (algebraMap S (Localization.Away f₀) y))` using `hyu.map φ`. Establish `hdu : IsUnit (φ d)`. Establish `h3 : φ d * φ (algebraMap S (Localization.Away f₀) y) = algebraMap S _ a`. Rewrite using `[← map_mul, hspec, AlgHom.commutes]`.

Conclude with `isUnit_of_mul_isUnit_left (h3 ▸ hau)`. Establish `hdvd : m i ∣ d` using `Finset.dvd_prod_of_mem m (Finset.mem_univ i)`. Conclude with `isUnit_of_dvd_unit (map_dvd φ hdvd) hdu`.
-/
theorem exists_basicOpen_isUnit_of_notMem_map :
    ∀ (S : Type) [CommRing S] (f₀ : S) (q : Ideal S), q.IsPrime → f₀ ∉ q →
      ∀ (J : Type) [Finite J] (m : J → Localization.Away f₀),
        (∀ i, m i ∉ Ideal.map (algebraMap S (Localization.Away f₀)) q) →
        ∃ f : S, f ∉ q ∧ ∃ φ : Localization.Away f₀ →ₐ[S] Localization.Away f,
          ∀ i, IsUnit (φ (m i)) := by
  intro S _ f₀ q hq hf₀ J _ m hm
  classical
  haveI := Fintype.ofFinite J
  have hdisj : Disjoint (↑(Submonoid.powers f₀) : Set S) ↑q :=
    (Ideal.disjoint_powers_iff_notMem f₀ hq.isRadical).2 hf₀
  haveI hq' : (Ideal.map (algebraMap S (Localization.Away f₀)) q).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f₀) (Localization.Away f₀) q hq hdisj
  set d : (Localization.Away f₀) := ∏ i, m i with hd
  have hdq : d ∉ Ideal.map (algebraMap S (Localization.Away f₀)) q := by
    intro h
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (p := Ideal.map (algebraMap S (Localization.Away f₀)) q)).1 h
    exact hm i hi
  obtain ⟨⟨a, y⟩, hay⟩ := IsLocalization.mk'_surjective (Submonoid.powers f₀) d
  simp only at hay
  have hspec : d * algebraMap S (Localization.Away f₀) y = algebraMap S (Localization.Away f₀) a := by
    rw [← hay]; exact IsLocalization.mk'_spec (Localization.Away f₀) a y
  have hyu : IsUnit (algebraMap S (Localization.Away f₀) y) := IsLocalization.map_units (Localization.Away f₀) y
  have ha : a ∉ q := by
    intro haq
    have h1 : algebraMap S (Localization.Away f₀) a ∈ Ideal.map (algebraMap S (Localization.Away f₀)) q := Ideal.mem_map_of_mem _ haq
    rw [← hspec] at h1
    rcases hq'.mem_or_mem h1 with h2 | h2
    · exact hdq h2
    · exact hq'.ne_top (Ideal.eq_top_of_isUnit_mem _ h2 hyu)
  refine ⟨f₀ * a, fun h => (hq.mem_or_mem h).elim hf₀ ha, ?_⟩
  let ψ : (Localization.Away f₀) →+* Localization.Away (f₀ * a) := IsLocalization.Away.awayToAwayRight f₀ a
  let φ : (Localization.Away f₀) →ₐ[S] Localization.Away (f₀ * a) :=
    { ψ with commutes' := fun r => IsLocalization.Away.awayToAwayRight_eq f₀ a r }
  refine ⟨φ, fun i => ?_⟩
  have hφ : ∀ x, φ x = ψ x := fun _ => rfl

  have hau : IsUnit (algebraMap S (Localization.Away (f₀ * a)) a) := by
    have hu : IsUnit (algebraMap S (Localization.Away (f₀ * a)) (f₀ * a)) :=
      IsLocalization.Away.algebraMap_isUnit (f₀ * a)
    rw [map_mul] at hu
    exact isUnit_of_mul_isUnit_right hu
  have hyu' : IsUnit (φ (algebraMap S (Localization.Away f₀) y)) := hyu.map φ
  have hdu : IsUnit (φ d) := by
    have h3 : φ d * φ (algebraMap S (Localization.Away f₀) y) = algebraMap S _ a := by
      rw [← map_mul, hspec, AlgHom.commutes]
    exact isUnit_of_mul_isUnit_left (h3 ▸ hau)
  have hdvd : m i ∣ d := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  exact isUnit_of_dvd_unit (map_dvd φ hdvd) hdu

end GlobalTheory
