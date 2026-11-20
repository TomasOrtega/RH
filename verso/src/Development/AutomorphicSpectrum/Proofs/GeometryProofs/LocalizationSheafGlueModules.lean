import Mathlib

namespace GlobalTheory.CompanionTheory.BasicCover

/- English proof (translation)
Consider the cases of `nonempty_fintype J`. Use `choose n hn using h`. Conclude with `⟨∑ j, n j, fun j => mono j _ _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)) (hn j)⟩`.
-/
theorem exists_uniform_bound {J : Type} [Finite J] (P : J → ℕ → Prop)
    (mono : ∀ j n m, n ≤ m → P j n → P j m) (h : ∀ j, ∃ n, P j n) : ∃ N, ∀ j, P j N := by
  classical
  cases nonempty_fintype J
  choose n hn using h
  exact ⟨∑ j, n j, fun j => mono j _ _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)) (hn j)⟩

/- English proof (translation)
Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hnm`. Rewrite using `[pow_add, mul_comm, mul_smul, h, smul_zero]`.
-/
theorem pow_smul_eq_zero_mono {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (t : R) (y : M) {n m : ℕ} (hnm : n ≤ m) (h : t ^ n • y = 0) : t ^ m • y = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [pow_add, mul_comm, mul_smul, h, smul_zero]

/- English proof (translation)
Take `⟨⟨c, hc⟩, hc'⟩` from `IsLocalizedModule.exists_of_eq (S := Submonoid.powers t) (f := φ) (x₁ := y) (x₂ := 0) (by rw [h, map_zero])`. Take `⟨n, rfl⟩` from `(Submonoid.mem_powers_iff _ _).1 hc`. Conclude with `⟨n, by simpa [Submonoid.smul_def] using hc'⟩`.
-/
theorem exists_pow_smul_eq_zero {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (t : R) (φ : M →ₗ[R] M')
    [IsLocalizedModule (Submonoid.powers t) φ] (y : M) (h : φ y = 0) :
    ∃ n : ℕ, t ^ n • y = 0 := by
  obtain ⟨⟨c, hc⟩, hc'⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers t) (f := φ)
    (x₁ := y) (x₂ := 0) (by rw [h, map_zero])
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hc
  exact ⟨n, by simpa [Submonoid.smul_def] using hc'⟩

/- English proof (translation)
Take `⟨⟨y, ⟨c, hc⟩⟩, hy⟩` from `IsLocalizedModule.surj (Submonoid.powers t) φ z`. Take `⟨n, rfl⟩` from `(Submonoid.mem_powers_iff _ _).1 hc`. Conclude with `⟨n, y, by simpa [Submonoid.smul_def] using hy⟩`.
-/
theorem exists_pow_smul_eq_map {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (t : R) (φ : M →ₗ[R] M')
    [IsLocalizedModule (Submonoid.powers t) φ] (z : M') :
    ∃ (n : ℕ) (y : M), t ^ n • z = φ y := by
  obtain ⟨⟨y, ⟨c, hc⟩⟩, hy⟩ := IsLocalizedModule.surj (Submonoid.powers t) φ z
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hc
  exact ⟨n, y, by simpa [Submonoid.smul_def] using hy⟩

/- English proof (translation)
Introduce `R E _ _ _ J _ f _ F _ _ res ρ _ hcomp hrρ hunit hloc hsep hglue i`. Establish `inj : ∀ (g g' : {g : R // ∃ i, f i ∣ g}) (h : g.1 ∣ g'.1) (t : R), g'.1 = g.1 * t → t ∣ g.1 → ∀ x, res g g' h x = 0 → x = 0`. Introduce `g g' h t ht htd x hx`. Use `hloc g g' h t ht` as an intermediate fact. Take `⟨n, hn⟩` from `GlobalTheory.CompanionTheory.BasicCover.exists_pow_smul_eq_zero t (res g g' h) x hx`.

Establish `hu : IsUnit (algebraMap R (Module.End R (F g)) (t ^ n))`. Rewrite using `[map_pow]`. Conclude with `(hunit g t htd).pow n`. Apply `((Module.End.isUnit_iff _).1 hu).1` to reduce the goal to its premises. Rewrite using `[Module.algebraMap_end_apply, hn, map_zero]`.

Use `⟨fun x => ?_, fun z => ?_, fun {x₁ x₂} hx => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `x`. Take `⟨n, rfl⟩` from `(Submonoid.mem_powers_iff _ _).1 hc`. Use `show IsUnit (algebraMap R (Module.End R (F ⟨f i, i, dvd_rfl⟩)) (f i ^ n))`. Rewrite using `[map_pow]`.

Conclude with `(hunit _ (f i) dvd_rfl).pow n`. Establish `Pex : ∀ j, ∃ n, (fun j n => ∃ y : F ⟨f j, j, dvd_rfl⟩, f i ^ n • res ⟨f i, i, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_right _ _) z = res ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_left _ _) y) j n`. Introduce `j`. Use `hloc ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_left _ _) (f i) (mul_comm _ _)` as an intermediate fact. Conclude with `GlobalTheory.CompanionTheory.BasicCover.exists_pow_smul_eq_map (f i) _ _`.

Take `⟨N, hN⟩` from `GlobalTheory.CompanionTheory.BasicCover.exists_uniform_bound (fun j n => ∃ y : F ⟨f j, j, dvd_rfl⟩, f i ^ n • res ⟨f i, i, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_right _ _) z = res ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_left _ _) y) (fun j n m h …`. Take `⟨y, hy⟩` from `hex`. Conclude with `⟨f i ^ (m - n) • y, by`. Rewrite using `[map_smul, ← hy, smul_smul, ← pow_add, Nat.sub_add_cancel hnm]⟩) Pex`. Use `choose y hy using hN`.

Establish `lift : ∀ j (g'' : {g : R // ∃ i, f i ∣ g}) (h1 : f j ∣ g''.1) (h2 : f i * f j ∣ g''.1) (h3 : f i ∣ g''.1), res ⟨f j, j, dvd_rfl⟩ g'' h1 (y j) = f i ^ N • res ⟨f i, i, dvd_rfl⟩ g'' h3 z`. Introduce `j g'' h1 h2 h3`. Rewrite using `[← hcomp ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ g'' (dvd_mul_left _ _) h2 h1 (y j), ← hy j, map_smul, hcomp ⟨f i, i, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ g'' (dvd_mul_right _ _) h2 h3 z]`. Establish `Qex : ∀ p : J × J, ∃ m, f i ^ m • (res ⟨f p.1, p.1, dvd_rfl⟩ ⟨f p.1 * f p.2, p.1, dvd_mul_right _ _⟩ (dvd_mul_right _ _) (y p.1) - res ⟨f p.2, p.2, dvd_rfl⟩ ⟨f p.1 * f p.2, p.1, dvd_mul_right _ _⟩ (dvd_mul_left _ _) (y p.2)) = 0`. Introduce and unpack `⟨j, k⟩`.

Simplify using `only`. Use `hloc ⟨f j * f k, j, dvd_mul_right _ _⟩ ⟨f j * f k * f i, j, dvd_mul_of_dvd_left (dvd_mul_right _ _) _⟩ (dvd_mul_right _ _) (f i) rfl` as an intermediate fact. Apply `GlobalTheory.CompanionTheory.BasicCover.exists_pow_smul_eq_zero (f i) (res ⟨f j * f k, j, dvd_mul_right _ _⟩ ⟨f j * f k * f i, j, dvd_mul_of_dvd_left (dvd_mul_right _ _) _⟩ (dvd_mul_right _ _))` to reduce the goal to its premises. Rewrite using `[map_sub, hcomp ⟨f j, j, dvd_rfl⟩ ⟨f j * f k, j, dvd_mul_right _ _⟩ ⟨f j * f k * f i, j, dvd_mul_of_dvd_left (dvd_mul_right _ _) _⟩ (dvd_mul_right _ _) (dvd_mul_right _ _) (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) (y j), hcomp ⟨f k, k, dvd_rfl⟩ ⟨f j * f k, j, dvd_mul_right _ _⟩ …`. Take `⟨M, hM⟩` from `GlobalTheory.CompanionTheory.BasicCover.exists_uniform_bound (fun (p : J × J) m => f i ^ m • (res ⟨f p.1, p.1, dvd_rfl⟩ ⟨f p.1 * f p.2, p.1, dvd_mul_right _ _⟩ (dvd_mul_right _ _) (y p.1) - res ⟨f p.2, p.2, dvd_rfl⟩ ⟨f p.1 * f p.2, p.1, dvd_mul_right _ _⟩ (dvd_mul_left _ _) (y p. …`.

Establish `hii : f i ^ N • z = y i`. Apply `sub_eq_zero.1` to reduce the goal to its premises. Apply `inj ⟨f i, i, dvd_rfl⟩ ⟨f i * f i, i, dvd_mul_right _ _⟩ (dvd_mul_right _ _) (f i) rfl dvd_rfl` to reduce the goal to its premises. Rewrite using `[map_sub, map_smul, hy i, sub_self]`. Take `⟨e, he⟩` from `hglue (fun j => f i ^ M • y j) fun j k => by`.

Establish `h4` using `hM (j, k)`. Simplify using `only at h4 ⊢`. Rewrite `h4` using `[smul_sub, sub_eq_zero]`. Rewrite using `[map_smul, map_smul]`. Conclude with `h4`.

Use `⟨(e, ⟨f i ^ (M + N), pow_mem (Submonoid.mem_powers _) _⟩), ?_⟩` and prove the remaining obligations. Use `show f i ^ (M + N) • z = ρ ⟨f i, i, dvd_rfl⟩ e`. Rewrite using `[he i]`. Rewrite using `[← hii, smul_smul, ← pow_add]`. Establish `hd : ρ ⟨f i, i, dvd_rfl⟩ (x₁ - x₂) = 0` using `by rw [map_sub, hx, sub_self]`.

Establish `Rj : ∀ j, ∃ n, f i ^ n • ρ ⟨f j, j, dvd_rfl⟩ (x₁ - x₂) = 0`. Introduce `j`. Use `hloc ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_left _ _) (f i) (mul_comm _ _)` as an intermediate fact. Apply `GlobalTheory.CompanionTheory.BasicCover.exists_pow_smul_eq_zero (f i) (res ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_left _ _))` to reduce the goal to its premises. Rewrite using `[hrρ, ← hrρ ⟨f i, i, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_right _ _), hd, map_zero]`.

Take `⟨N, hN⟩` from `GlobalTheory.CompanionTheory.BasicCover.exists_uniform_bound (fun j n => f i ^ n • ρ ⟨f j, j, dvd_rfl⟩ (x₁ - x₂) = 0) (fun j n m hnm hn => GlobalTheory.CompanionTheory.BasicCover.pow_smul_eq_zero_mono _ _ hnm hn) Rj`. Establish `h0 : f i ^ N • (x₁ - x₂) = 0` using `hsep _ fun j => by rw [map_smul]; exact hN j`. Use `⟨⟨f i ^ N, pow_mem (Submonoid.mem_powers _) N⟩, ?_⟩` and prove the remaining obligations. Use `show f i ^ N • x₁ = f i ^ N • x₂`. Rewrite using `[← sub_eq_zero, ← smul_sub]`.

Conclude with `h0`.
-/
theorem isLocalizedModule_of_basic_cover : ∀ (R E : Type) [CommRing R] [AddCommGroup E] [Module R E] (J : Type) [Finite J] (f : J → R), Ideal.span (Set.range f) = ⊤ →
  ∀ (F : {g : R // ∃ i, f i ∣ g} → Type) [∀ g, AddCommGroup (F g)] [∀ g, Module R (F g)]
    (res : ∀ g g' : {g : R // ∃ i, f i ∣ g}, g.1 ∣ g'.1 → (F g →ₗ[R] F g'))
    (ρ : ∀ g, E →ₗ[R] F g),
    (∀ g (h : g.1 ∣ g.1) y, res g g h y = y) →
    (∀ g g' g'' (h : g.1 ∣ g'.1) (h' : g'.1 ∣ g''.1) (h'' : g.1 ∣ g''.1) y, res g' g'' h' (res g g' h y) = res g g'' h'' y) →
    (∀ g g' (h : g.1 ∣ g'.1) e, res g g' h (ρ g e) = ρ g' e) →
    (∀ g (a : R), a ∣ g.1 → IsUnit (algebraMap R (Module.End R (F g)) a)) →
    (∀ g g' (h : g.1 ∣ g'.1) (t : R), g'.1 = g.1 * t → IsLocalizedModule (Submonoid.powers t) (res g g' h)) →
    (∀ e, (∀ i, ρ ⟨f i, i, dvd_rfl⟩ e = 0) → e = 0) →
    (∀ w : ∀ i, F ⟨f i, i, dvd_rfl⟩,
      (∀ i j, res ⟨f i, i, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_right _ _) (w i) =
        res ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_left _ _) (w j)) →
      ∃ e, ∀ i, ρ ⟨f i, i, dvd_rfl⟩ e = w i) →
    ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (ρ ⟨f i, i, dvd_rfl⟩) := by
  intro R E _ _ _ J _ f _ F _ _ res ρ _ hcomp hrρ hunit hloc hsep hglue i
  have inj : ∀ (g g' : {g : R // ∃ i, f i ∣ g}) (h : g.1 ∣ g'.1) (t : R), g'.1 = g.1 * t → t ∣ g.1 →
      ∀ x, res g g' h x = 0 → x = 0 := by
    intro g g' h t ht htd x hx
    have := hloc g g' h t ht
    obtain ⟨n, hn⟩ := GlobalTheory.CompanionTheory.BasicCover.exists_pow_smul_eq_zero t (res g g' h) x hx
    have hu : IsUnit (algebraMap R (Module.End R (F g)) (t ^ n)) := by
      rw [map_pow]
      exact (hunit g t htd).pow n
    apply ((Module.End.isUnit_iff _).1 hu).1
    rw [Module.algebraMap_end_apply, hn, map_zero]
  refine ⟨fun x => ?_, fun z => ?_, fun {x₁ x₂} hx => ?_⟩
  · obtain ⟨c, hc⟩ := x
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hc
    show IsUnit (algebraMap R (Module.End R (F ⟨f i, i, dvd_rfl⟩)) (f i ^ n))
    rw [map_pow]
    exact (hunit _ (f i) dvd_rfl).pow n
  · have Pex : ∀ j, ∃ n, (fun j n => ∃ y : F ⟨f j, j, dvd_rfl⟩, f i ^ n • res ⟨f i, i, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_right _ _) z = res ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_left _ _) y) j n := by
      intro j
      have := hloc ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_left _ _) (f i) (mul_comm _ _)
      exact GlobalTheory.CompanionTheory.BasicCover.exists_pow_smul_eq_map (f i) _ _
    obtain ⟨N, hN⟩ := GlobalTheory.CompanionTheory.BasicCover.exists_uniform_bound (fun j n => ∃ y : F ⟨f j, j, dvd_rfl⟩, f i ^ n • res ⟨f i, i, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_right _ _) z = res ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_left _ _) y)
      (fun j n m hnm hex => by
        obtain ⟨y, hy⟩ := hex
        exact ⟨f i ^ (m - n) • y, by
          rw [map_smul, ← hy, smul_smul, ← pow_add, Nat.sub_add_cancel hnm]⟩) Pex
    choose y hy using hN
    have lift : ∀ j (g'' : {g : R // ∃ i, f i ∣ g}) (h1 : f j ∣ g''.1) (h2 : f i * f j ∣ g''.1)
        (h3 : f i ∣ g''.1), res ⟨f j, j, dvd_rfl⟩ g'' h1 (y j) = f i ^ N • res ⟨f i, i, dvd_rfl⟩ g'' h3 z := by
      intro j g'' h1 h2 h3
      rw [← hcomp ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ g'' (dvd_mul_left _ _) h2 h1 (y j), ← hy j, map_smul,
        hcomp ⟨f i, i, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ g'' (dvd_mul_right _ _) h2 h3 z]
    have Qex : ∀ p : J × J, ∃ m, f i ^ m • (res ⟨f p.1, p.1, dvd_rfl⟩ ⟨f p.1 * f p.2, p.1, dvd_mul_right _ _⟩ (dvd_mul_right _ _) (y p.1) - res ⟨f p.2, p.2, dvd_rfl⟩ ⟨f p.1 * f p.2, p.1, dvd_mul_right _ _⟩ (dvd_mul_left _ _) (y p.2)) = 0 := by
      rintro ⟨j, k⟩
      dsimp only
      have := hloc ⟨f j * f k, j, dvd_mul_right _ _⟩ ⟨f j * f k * f i, j, dvd_mul_of_dvd_left (dvd_mul_right _ _) _⟩ (dvd_mul_right _ _) (f i) rfl
      apply GlobalTheory.CompanionTheory.BasicCover.exists_pow_smul_eq_zero (f i) (res ⟨f j * f k, j, dvd_mul_right _ _⟩ ⟨f j * f k * f i, j, dvd_mul_of_dvd_left (dvd_mul_right _ _) _⟩ (dvd_mul_right _ _))
      rw [map_sub, hcomp ⟨f j, j, dvd_rfl⟩ ⟨f j * f k, j, dvd_mul_right _ _⟩ ⟨f j * f k * f i, j, dvd_mul_of_dvd_left (dvd_mul_right _ _) _⟩ (dvd_mul_right _ _) (dvd_mul_right _ _)
          (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) (y j),
        hcomp ⟨f k, k, dvd_rfl⟩ ⟨f j * f k, j, dvd_mul_right _ _⟩ ⟨f j * f k * f i, j, dvd_mul_of_dvd_left (dvd_mul_right _ _) _⟩ (dvd_mul_left _ _) (dvd_mul_right _ _)
          (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) (y k),
        lift j ⟨f j * f k * f i, j, dvd_mul_of_dvd_left (dvd_mul_right _ _) _⟩ (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)
          (Dvd.intro (f k) (show f i * f j * f k = f j * f k * f i by ring))
          (Dvd.intro (f j * f k) (show f i * (f j * f k) = f j * f k * f i by ring)),
        lift k ⟨f j * f k * f i, j, dvd_mul_of_dvd_left (dvd_mul_right _ _) _⟩ (dvd_mul_of_dvd_left (dvd_mul_left _ _) _)
          (Dvd.intro (f j) (show f i * f k * f j = f j * f k * f i by ring))
          (Dvd.intro (f j * f k) (show f i * (f j * f k) = f j * f k * f i by ring)), sub_self]
    obtain ⟨M, hM⟩ := GlobalTheory.CompanionTheory.BasicCover.exists_uniform_bound
      (fun (p : J × J) m => f i ^ m • (res ⟨f p.1, p.1, dvd_rfl⟩ ⟨f p.1 * f p.2, p.1, dvd_mul_right _ _⟩ (dvd_mul_right _ _) (y p.1) - res ⟨f p.2, p.2, dvd_rfl⟩ ⟨f p.1 * f p.2, p.1, dvd_mul_right _ _⟩ (dvd_mul_left _ _) (y p.2)) = 0)
      (fun p n m hnm hn => GlobalTheory.CompanionTheory.BasicCover.pow_smul_eq_zero_mono _ _ hnm hn) Qex
    have hii : f i ^ N • z = y i := by
      apply sub_eq_zero.1
      apply inj ⟨f i, i, dvd_rfl⟩ ⟨f i * f i, i, dvd_mul_right _ _⟩ (dvd_mul_right _ _) (f i) rfl dvd_rfl
      rw [map_sub, map_smul, hy i, sub_self]
    obtain ⟨e, he⟩ := hglue (fun j => f i ^ M • y j) fun j k => by
      have h4 := hM (j, k)
      dsimp only at h4 ⊢
      rw [smul_sub, sub_eq_zero] at h4
      rw [map_smul, map_smul]
      exact h4
    refine ⟨(e, ⟨f i ^ (M + N), pow_mem (Submonoid.mem_powers _) _⟩), ?_⟩
    show f i ^ (M + N) • z = ρ ⟨f i, i, dvd_rfl⟩ e
    rw [he i]
    rw [← hii, smul_smul, ← pow_add]
  · have hd : ρ ⟨f i, i, dvd_rfl⟩ (x₁ - x₂) = 0 := by rw [map_sub, hx, sub_self]
    have Rj : ∀ j, ∃ n, f i ^ n • ρ ⟨f j, j, dvd_rfl⟩ (x₁ - x₂) = 0 := by
      intro j
      have := hloc ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_left _ _) (f i) (mul_comm _ _)
      apply GlobalTheory.CompanionTheory.BasicCover.exists_pow_smul_eq_zero (f i)
        (res ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_left _ _))
      rw [hrρ, ← hrρ ⟨f i, i, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_right _ _), hd, map_zero]
    obtain ⟨N, hN⟩ := GlobalTheory.CompanionTheory.BasicCover.exists_uniform_bound
      (fun j n => f i ^ n • ρ ⟨f j, j, dvd_rfl⟩ (x₁ - x₂) = 0)
      (fun j n m hnm hn => GlobalTheory.CompanionTheory.BasicCover.pow_smul_eq_zero_mono _ _ hnm hn) Rj
    have h0 : f i ^ N • (x₁ - x₂) = 0 := hsep _ fun j => by rw [map_smul]; exact hN j
    refine ⟨⟨f i ^ N, pow_mem (Submonoid.mem_powers _) N⟩, ?_⟩
    show f i ^ N • x₁ = f i ^ N • x₂
    rw [← sub_eq_zero, ← smul_sub]
    exact h0

end GlobalTheory.CompanionTheory.BasicCover
