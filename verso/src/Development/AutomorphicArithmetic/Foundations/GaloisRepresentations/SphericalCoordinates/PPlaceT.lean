import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

/- English proof (translation)
Introduce `hc`. Establish `him : r.im = 0` using `Complex.conj_eq_iff_im.mp hc`. Apply the tactic sequence `obtain ⟨x, rfl⟩ : ∃ x : ℝ, r = (x : ℂ) := ⟨r.re, by apply Complex.ext <;> simp [him]⟩`. Establish `h1 : x ^ 2 - (tr : ℝ) * x + (nm : ℝ) = 0` using `by exact_mod_cast hr`. Establish `h2 : ((tr : ℝ)) ^ 2 - 4 * (nm : ℝ) < 0` using `by exact_mod_cast hd`.

Use polynomial arithmetic with `[sq_nonneg (2 * x - (tr : ℝ))]`.
-/
private theorem rho_not_real {tr nm : ℤ} {r : ℂ} (hd : tr ^ 2 - 4 * nm < 0)
    (hr : r ^ 2 - (tr : ℂ) * r + (nm : ℂ) = 0) : (starRingEnd ℂ) r ≠ r := by
  intro hc
  have him : r.im = 0 := Complex.conj_eq_iff_im.mp hc
  obtain ⟨x, rfl⟩ : ∃ x : ℝ, r = (x : ℂ) := ⟨r.re, by apply Complex.ext <;> simp [him]⟩
  have h1 : x ^ 2 - (tr : ℝ) * x + (nm : ℝ) = 0 := by exact_mod_cast hr
  have h2 : ((tr : ℝ)) ^ 2 - 4 * (nm : ℝ) < 0 := by exact_mod_cast hd
  nlinarith [sq_nonneg (2 * x - (tr : ℝ))]

/- English proof (translation)
Introduce `p _ D G L ha v hv t₀ ht`. Establish `i₀ : Fin D.a` using `⟨0, by omega⟩`. Establish `hsub : ∀ i j : Fin D.a, i = j` using `fun i j => by`. Apply `Fin.ext` to reduce the goal to its premises. Use `i.2` as an intermediate fact.

Use `j.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hρ : t₀ (D.ω : D.F) = D.ρc` using `by rw [← ht i₀]; exact D.tau_ω i₀`. Establish `hne : (starRingEnd ℂ) D.ρc ≠ D.ρc` using `rho_not_real D.disc_neg D.ρc_root`. Take `⟨i, hi⟩` from `(L.sig v).1 hv`.

Establish `hφ : ∀ x, (G.iotaC.comp (L.s i)) (L.e x) = t₀ x` using `fun x => by`. Rewrite using `[← ht i]`. Conclude with `L.s_C i x`. Use `⟨fun v' hv' => ?_, hρ, hne, ?_⟩` and prove the remaining obligations. Take `⟨j, hj⟩` from `(L.sig v').1 hv'`.

Rewrite using `[hi, hj, hsub i j]`. Establish `hemb` using `InfinitePlace.embedding_mk_eq (G.iotaC.comp (L.s i))`. Rewrite `hemb` using `[← hi]`. Break down `hemb with h | h` into its components or cases. Use `left`.

Establish `hx : ∀ x, v.embedding (L.e x) = t₀ x` using `fun x => by rw [h]; exact hφ x`. Use `⟨?_, hx⟩` and prove the remaining obligations. Unfold `sgnV`. Rewrite using `[if_pos (by rw [hx, hρ])]`. Use `right`.

Establish `hx : ∀ x, v.embedding (L.e x) = (starRingEnd ℂ) (t₀ x)` using `fun x => by`. Rewrite using `[h, ComplexEmbedding.conjugate_coe_eq, hφ]`. Establish `hω : v.embedding (L.e (D.ω : D.F)) ≠ D.ρc` using `by rw [hx, hρ]; exact hne`. Use `⟨?_, fun hall => hω (by rw [hall, hρ]), fun x => by rw [hx, Complex.conj_conj]⟩` and prove the remaining obligations. Unfold `sgnV`.

Rewrite using `[if_neg hω]`.
-/
theorem UpperTheory.Gal.W2.placeT_of :
    UpperTheory.Gal.W2.PlaceT := by
  intro p _ D G L ha v hv t₀ ht
  have i₀ : Fin D.a := ⟨0, by omega⟩
  have hsub : ∀ i j : Fin D.a, i = j := fun i j => by
    apply Fin.ext; have := i.2; have := j.2; omega
  have hρ : t₀ (D.ω : D.F) = D.ρc := by rw [← ht i₀]; exact D.tau_ω i₀
  have hne : (starRingEnd ℂ) D.ρc ≠ D.ρc := rho_not_real D.disc_neg D.ρc_root
  obtain ⟨i, hi⟩ := (L.sig v).1 hv
  have hφ : ∀ x, (G.iotaC.comp (L.s i)) (L.e x) = t₀ x := fun x => by
    rw [← ht i]; exact L.s_C i x
  refine ⟨fun v' hv' => ?_, hρ, hne, ?_⟩
  · obtain ⟨j, hj⟩ := (L.sig v').1 hv'
    rw [hi, hj, hsub i j]
  · have hemb := InfinitePlace.embedding_mk_eq (G.iotaC.comp (L.s i))
    rw [← hi] at hemb
    rcases hemb with h | h
    · left
      have hx : ∀ x, v.embedding (L.e x) = t₀ x := fun x => by rw [h]; exact hφ x
      refine ⟨?_, hx⟩
      unfold sgnV
      rw [if_pos (by rw [hx, hρ])]
    · right
      have hx : ∀ x, v.embedding (L.e x) = (starRingEnd ℂ) (t₀ x) := fun x => by
        rw [h, ComplexEmbedding.conjugate_coe_eq, hφ]
      have hω : v.embedding (L.e (D.ω : D.F)) ≠ D.ρc := by rw [hx, hρ]; exact hne
      refine ⟨?_, fun hall => hω (by rw [hall, hρ]), fun x => by rw [hx, Complex.conj_conj]⟩
      unfold sgnV
      rw [if_neg hω]
