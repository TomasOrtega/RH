import Development.EtaleCohomology.KummerTheory.InjSlice

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory

/- English proof (translation)
Take `⟨m, rfl⟩` from `hd`. Use `⟨fun a ha => by rw [mul_comm, mul_smul, h.1 a ha, smul_zero], fun b => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `h.2 (m • b)`. Conclude with `⟨a, by rw [ha, mul_smul]⟩`.
-/
theorem IsoUpTo.comb_mono {q : ℕ} {E : Spc} {n i : ℤ} {r : ℕ} {c : Fin r → Ht q E n i} {N N' : ℕ} (hd : N ∣ N')
    (h : IsoUpTo N (comb q c)) : IsoUpTo N' (comb q c) := by
  obtain ⟨m, rfl⟩ := hd
  refine ⟨fun a ha => by rw [mul_comm, mul_smul, h.1 a ha, smul_zero], fun b => ?_⟩
  obtain ⟨a, ha⟩ := h.2 (m • b)
  exact ⟨a, by rw [ha, mul_smul]⟩

/- English proof (translation)
Introduce `U ⟨x⟩`. Establish `h` using `hl.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ ((show U ⟶ X from x) ≫ p).appTop).hom`. Rewrite `h` using `[map_natCast]`. Then use the resulting hypothesis.
-/
theorem inv_of_field (l : ℕ) (k : Type) [Field k] (hl : IsUnit (l : k)) {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) : Inv l (sch.obj X) := by
  intro U ⟨x⟩
  have h := hl.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ ((show U ⟶ X from x) ≫ p).appTop).hom
  rwa [map_natCast] at h

/- English proof (translation)
Introduce `a2 a6n a6r a7 a8 a9 a10 a11 b1 b2 b3 e2 e3 e4 l _ k _ _ hl X Y pX pY _ _ _ n i`. Establish `hne : ∀ j : ℕ, NeZero (l ^ j)` using `fun j => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Establish `hu : ∀ j : ℕ, IsUnit ((l ^ j : ℕ) : k)` using `fun j => by rw [Nat.cast_pow]; exact hl.pow j`. Establish `hA` using `hAd a11 l (sch.obj X) i (fun b => hB a7 a8 a10 a11 l b _ i (inv_of_field l k hl pX)) (fun j m => e4 (l ^ j) k (hu j) pX m i)`. Use `choose r c N hN hQ hI using hA`.

Take `⟨e, he⟩` from `hLH a2 a6n b1`. Set `M : ℕ` to `n.toNat + 1`. Set `N' : ℕ` to `∏ a ∈ Finset.range (M + 1), N (a : ℕ)`. Establish `hN' : 0 < N'` using `Finset.prod_pos fun a _ => hN _`. Use `hL a9 a11 l pX pY n i M (N' ^ e M) (fun a => r a) (fun a => c a) (by omega) (pow_pos hN' _) (fun a _ => hQ _) (fun j m => e4 (l ^ j) k (hu j) pY m 0) fun j => ?_` and prove the remaining obligations.

Use `he (l ^ j) pX (hu j) i _ _ M N' (fun A s hA m hm => ?_) pY n (by omega)` and prove the remaining obligations. Conclude with `hSt a6n a6r a9 b2 (l ^ j) pX A s hA (hu j) i _ _ M N' (hInv a9 b2 b3 e2 e3 (l ^ j) k (hu j) pX A s hA i) (fun a ha => (hI a j).comb_mono (Finset.dvd_prod_of_mem _ (Finset.mem_range.2 (by omega)))) m hm`.
-/
theorem goal_of (hLH : LH) (hInv : SHInv) (hSt : Stalk) (hB : Bock) (hAd : AdicDeg) (hL : Limit) : GOAL := by
  intro a2 a6n a6r a7 a8 a9 a10 a11 b1 b2 b3 e2 e3 e4 l _ k _ _ hl X Y pX pY _ _ _ n i
  have hne : ∀ j : ℕ, NeZero (l ^ j) := fun j => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hu : ∀ j : ℕ, IsUnit ((l ^ j : ℕ) : k) := fun j => by rw [Nat.cast_pow]; exact hl.pow j
  have hA := hAd a11 l (sch.obj X) i (fun b => hB a7 a8 a10 a11 l b _ i (inv_of_field l k hl pX))
    (fun j m => e4 (l ^ j) k (hu j) pX m i)
  choose r c N hN hQ hI using hA
  obtain ⟨e, he⟩ := hLH a2 a6n b1
  let M : ℕ := n.toNat + 1
  let N' : ℕ := ∏ a ∈ Finset.range (M + 1), N (a : ℕ)
  have hN' : 0 < N' := Finset.prod_pos fun a _ => hN _
  refine hL a9 a11 l pX pY n i M (N' ^ e M) (fun a => r a) (fun a => c a) (by omega) (pow_pos hN' _) (fun a _ => hQ _)
    (fun j m => e4 (l ^ j) k (hu j) pY m 0) fun j => ?_
  refine he (l ^ j) pX (hu j) i _ _ M N' (fun A s hA m hm => ?_) pY n (by omega)
  exact hSt a6n a6r a9 b2 (l ^ j) pX A s hA (hu j) i _ _ M N' (hInv a9 b2 b3 e2 e3 (l ^ j) k (hu j) pX A s hA i)
    (fun a ha => (hI a j).comb_mono (Finset.dvd_prod_of_mem _ (Finset.mem_range.2 (by omega)))) m hm

end LateralTheory.KummerTheory

end
