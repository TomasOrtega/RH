import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.SeqColim

/- English proof (translation)
The claim follows from `| 0, x => rfl | k + 1, x => by show ι (n + k + 1) (f (n + k) (tr f n k x)) = ι n x rw [h.comm, map_tr f ι h n k x]`.
-/
theorem map_tr {A : Type} [CommRing A] {G : ℕ → Type} [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)]
    (f : ∀ n, G n →ₐ[A] G (n + 1)) {L : Type} [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L)
    (h : IsColim f ι) (n : ℕ) : ∀ (k : ℕ) (x : G n), ι (n + k) (tr f n k x) = ι n x
  | 0, x => rfl
  | k + 1, x => by
      show ι (n + k + 1) (f (n + k) (tr f n k x)) = ι n x
      rw [h.comm, map_tr f ι h n k x]

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `congrArg (ι 0) (hG 0).char` as an intermediate fact. Simplify using `using this`. Introduce `x y hxy`. Take `⟨n, z, hz⟩` from `h.surj 2 ![x, y]`.

Establish `h0 : ι n (z 0 ^ p - z 1 ^ p) = 0`. Establish `e0` using `hz 0`. Establish `e1` using `hz 1`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1`. Simplify using `[map_sub, map_pow, e0, e1, hxy]`.

Take `⟨k, hk⟩` from `h.ker n 1 (fun _ => z 0 ^ p - z 1 ^ p) (fun _ => h0)`. Establish `hk0` using `hk 0`. Simplify using `only [map_sub, map_pow, sub_eq_zero] at hk0`. Establish `heq` using `(hG (n + k)).bij.1 hk0`. Establish `e0` using `hz 0`.

Establish `e1` using `hz 1`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1`. Use `congrArg (ι (n + k)) heq` as an intermediate fact. Rewrite `this` using `[map_tr f ι h, map_tr f ι h, e0, e1]`. Conclude with `this`.

Introduce `x`. Take `⟨n, z, hz⟩` from `h.surj 1 (fun _ => x)`. Take `⟨w, hw⟩` from `(hG n).bij.2 (z 0)`. Use `⟨ι n w, ?_⟩` and prove the remaining obligations. Simplify using `only at hw ⊢`.

Rewrite using `[← map_pow, hw, hz 0]`.
-/
theorem pf_of_stages (p : ℕ) {A : Type} [CommRing A] {G : ℕ → Type} [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)]
    (f : ∀ n, G n →ₐ[A] G (n + 1)) {L : Type} [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L)
    (h : IsColim f ι) (hG : ∀ n, Pf p (G n)) : Pf p L := by
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (ι 0) (hG 0).char
    simpa using this
  · intro x y hxy
    obtain ⟨n, z, hz⟩ := h.surj 2 ![x, y]
    have h0 : ι n (z 0 ^ p - z 1 ^ p) = 0 := by
      have e0 := hz 0
      have e1 := hz 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
      simp [map_sub, map_pow, e0, e1, hxy]
    obtain ⟨k, hk⟩ := h.ker n 1 (fun _ => z 0 ^ p - z 1 ^ p) (fun _ => h0)
    have hk0 := hk 0
    simp only [map_sub, map_pow, sub_eq_zero] at hk0
    have heq := (hG (n + k)).bij.1 hk0
    have e0 := hz 0
    have e1 := hz 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
    have := congrArg (ι (n + k)) heq
    rw [map_tr f ι h, map_tr f ι h, e0, e1] at this
    exact this
  · intro x
    obtain ⟨n, z, hz⟩ := h.surj 1 (fun _ => x)
    obtain ⟨w, hw⟩ := (hG n).bij.2 (z 0)
    refine ⟨ι n w, ?_⟩
    simp only at hw ⊢
    rw [← map_pow, hw, hz 0]

/- English proof (translation)
Take `⟨y, hy⟩` from `hs`. Take `⟨N₀, z, hz⟩` from `h.surj n y`. Establish `hd : ∀ i, ι N₀ ((∑ j, a i j • z j) - algebraMap A (G N₀) (c i)) = 0`. Introduce `i`. Simplify using `only [map_sub, map_sum, map_smul, AlgHom.commutes, hz, hy i, sub_self]`.

Take `⟨k, hk⟩` from `h.ker N₀ m _ hd`. Use `⟨N₀ + k, fun j => tr f N₀ k (z j), fun i => ?_⟩` and prove the remaining obligations. Use `hk i` as an intermediate fact. Simplify using `only [map_sub, map_sum, map_smul, AlgHom.commutes, sub_eq_zero] at this`. Conclude with `this`.
-/
theorem solv_at_stage {A : Type} [CommRing A] {G : ℕ → Type} [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)]
    (f : ∀ n, G n →ₐ[A] G (n + 1)) {L : Type} [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L)
    (h : IsColim f ι) (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A) (hs : Solv L a c) :
    ∃ N, Solv (G N) a c := by
  obtain ⟨y, hy⟩ := hs
  obtain ⟨N₀, z, hz⟩ := h.surj n y
  have hd : ∀ i, ι N₀ ((∑ j, a i j • z j) - algebraMap A (G N₀) (c i)) = 0 := by
    intro i
    simp only [map_sub, map_sum, map_smul, AlgHom.commutes, hz, hy i, sub_self]
  obtain ⟨k, hk⟩ := h.ker N₀ m _ hd
  refine ⟨N₀ + k, fun j => tr f N₀ k (z j), fun i => ?_⟩
  have := hk i
  simp only [map_sub, map_sum, map_smul, AlgHom.commutes, sub_eq_zero] at this
  exact this

end GlobalTheory.CompanionTheory.SeqColim

namespace GlobalTheory.CompanionTheory

/- English proof (translation)
Introduce `p _ A _ G _ _ f L _ _ ι h`. Conclude with `⟨SeqColim.pf_of_stages p f ι h, fun m n a c hs => SeqColim.solv_at_stage f ι h m n a c hs⟩`.
-/
theorem colim_pf : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](G : ℕ → Type) [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)] (f : ∀ n, G n →ₐ[A] G (n + 1))(L : Type) [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L), IsColim f ι → ((∀ n, Pf p (G n)) → Pf p L) ∧ ∀ (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), Solv L a c → ∃ N, Solv (G N) a c := by
  intro p _ A _ G _ _ f L _ _ ι h
  exact ⟨SeqColim.pf_of_stages p f ι h, fun m n a c hs => SeqColim.solv_at_stage f ι h m n a c hs⟩

end GlobalTheory.CompanionTheory
