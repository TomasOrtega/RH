import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

/- English proof (translation)
Simplify using `[img]`.
-/
private lemma card_img {κ : Type} [LinearOrder κ] {d : ℕ} (e : Fin d ↪o κ) : (img e).card = d := by
  simp [img]

/- English proof (translation)
Establish `h` using `card_img e`. Establish `hu : e = (img e).orderEmbOfFin h` using `Finset.orderEmbOfFin_unique' h (fun x => by simp [img])`. Rewrite using `[detC, dif_pos h]`. Use `congr 1`. Use extensionality with `a b`.

Simplify using `only [Matrix.of_apply]`. Rewrite using `[← hu, hA]`.
-/
private lemma detC_img {S κ : Type} [CommRing S] [LinearOrder κ] {d : ℕ} (ρ : κ → Fin d → S) (e : Fin d ↪o κ)
    (A : Matrix (Fin d) (Fin d) S) (hA : ∀ a, ρ (e a) = A a) : detC ρ (img e) = A.det := by
  have h := card_img e
  have hu : e = (img e).orderEmbOfFin h :=
    Finset.orderEmbOfFin_unique' h (fun x => by simp [img])
  rw [detC, dif_pos h]
  congr 1
  ext a b
  simp only [Matrix.of_apply]
  rw [← hu, hA]

/- English proof (translation)
Unfold `detC`. Use `split_ifs with hs`. Rewrite using `[Matrix.det_apply']`. Conclude with `R.sum_mem fun σ _ => R.mul_mem (intCast_mem R _) (R.prod_mem fun i _ => h _ _)`. Conclude with `R.zero_mem`.
-/
private lemma detC_mem {S κ : Type} [CommRing S] [Algebra ℂ S] [LinearOrder κ] {d : ℕ} (R : Subalgebra ℂ S)
    (ρ : κ → Fin d → S) (h : ∀ l b, ρ l b ∈ R) (s : Finset κ) : detC ρ s ∈ R := by
  unfold detC
  split_ifs with hs
  · rw [Matrix.det_apply']
    exact R.sum_mem fun σ _ => R.mul_mem (intCast_mem R _) (R.prod_mem fun i _ => h _ _)
  · exact R.zero_mem

/- English proof (translation)
Establish `hcC : ∀ s : Finset κ, c s ∈ (if (s.card : ℤ) = (d : ℤ) then M else ⊥)` using `fun s => (Submodule.mem_inf.1 hc).1 s (Set.mem_univ _)`. Establish `hcD : wd (fun l => act (r l)) c = 0` using `(Submodule.mem_inf.1 hc).2`. Take `⟨m, hm⟩ : ∃ m, m = c ((img e0).map ι.toEmbedding)` from `⟨_, rfl⟩`. Rewrite using `[← hm]`. Establish `hmM : m ∈ M`.

Use `hcC ((img e0).map ι.toEmbedding)` as an intermediate fact. Rewrite `this` using `[if_pos (by simp [card_img])]`. Rewrite using `[hm]` and apply the resulting hypothesis. Establish `hZ0 : (fun t : Finset κ0 => c (t.map ι.toEmbedding)) ∈ (kos act M fun l => r (ι l)).Z d`. Use `Submodule.mem_inf.2 ⟨fun s _ => ?_, ?_⟩` and prove the remaining obligations.

Use `hcC (s.map ι.toEmbedding)` as an intermediate fact. Simplify using `using this`. Use `show wd (fun l => act (r (ι l))) (fun t : Finset κ0 => c (t.map ι.toEmbedding)) = 0`. Use function extensionality and compare the values at `s`. Use `(hWB κ E (fun _ => M) (fun l => act (r l))).2.2.2.2.2 κ0 ι c s` as an intermediate fact.

Rewrite using `[this, hcD]`. Both sides reduce to the same expression. Establish `hZ' : (fun s : Finset κ0 => act (detC ρ s) m) ∈ (kos act M fun l => r (ι l)).Z d`. Use `Submodule.mem_inf.2 ⟨fun s _ => ?_, ?_⟩` and prove the remaining obligations. Use `show act (detC ρ s) m ∈ (if (s.card : ℤ) = (d : ℤ) then M else ⊥) split_ifs with hs`.

Conclude with `hSt _ (detC_mem R ρ hρ s) m hmM`. Establish `: s.card ≠ d` using `fun h => hs (by rw [h])`. Simplify using `[detC, this]`. Use `show wd (fun l => act (r (ι l))) (fun s : Finset κ0 => act (detC ρ s) m) = 0`. Use `hDet S E act κ0 d ρ (fun b => r (ι (e0 b))) m` as an intermediate fact.

Rewrite using `[show (fun l => act (∑ b, ρ l b * r (ι (e0 b)))) = fun l => act (r (ι l)) from` and apply the resulting hypothesis. Use function extensionality and compare the values at `fun l => by rw [hrel l]] at this`. Establish `hB` using `hK2 S E act κ0 R M (fun l => r (ι l)) d e0 hSt (fun l => hr _) hKE _ (Submodule.sub_mem _ hZ0 hZ') (by`. Establish `h1' : detC ρ (img e0) = 1`. Rewrite using `[detC_img ρ e0 1 (fun a => by rw [h1 a]; ext b; simp [Matrix.one_apply, Pi.single_apply, eq_comm])]`.

Simplify using the standard rewrite rules. Simplify using `only [Pi.sub_apply, h1', map_one, Module.End.one_apply, ← hm, sub_self]`. Conclude with `Submodule.zero_mem _)`. Establish `hval` using `(hKS S E act κ0 R M (fun l => r (ι l)) hSt (fun l => hr _)).2 d _ hB (img e0')`. Establish `hdet : detC ρ (img e0') = N.det` using `detC_img ρ e0' N h2`.

Simplify using `only [Pi.sub_apply, hdet] at hval`. Use `(?_ : sm act M (Set.range fun l => r (ι l)) ≤ sm act M (Set.range fun j => r (ι (e0 j)))) hval` and prove the remaining obligations. Unfold `sm`. Use `iSup₂_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨l, rfl⟩ _ ⟨x, hx, rfl⟩`.

Use `show act (r (ι l)) x ∈ _`. Rewrite using `[hrel l, map_sum, LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun b _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm, map_mul, Module.End.mul_apply]`. Conclude with `(le_iSup₂_of_le (f := fun (t : S) (_ : t ∈ Set.range fun j => r (ι (e0 j))) => M.map (act t)) (r (ι (e0 b))) ⟨b, rfl⟩ le_rfl) (Submodule.mem_map_of_mem (hSt _ (hρ l b) x hx))`.
-/
private lemma core (hDet : Det) (hK2 : KoszulBoundaryOfComponentMemIdeal) (hKS : KSub) (hWB : WdBasic)
    {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E)
    {κ κ0 : Type} [LinearOrder κ] [Fintype κ] [LinearOrder κ0] [Fintype κ0]
    (R : Subalgebra ℂ S) (M : Submodule ℂ E) (r : κ → S) {d : ℕ} (ι : κ0 ↪o κ) (e0 e0' : Fin d ↪o κ0)
    (N : Matrix (Fin d) (Fin d) S) (ρ : κ0 → Fin d → S)
    (h1 : ∀ j, ρ (e0 j) = Pi.single j 1) (h2 : ∀ a, ρ (e0' a) = N a) (hρ : ∀ l b, ρ l b ∈ R)
    (hrel : ∀ l, r (ι l) = ∑ b, ρ l b * r (ι (e0 b)))
    (hSt : Stab act R M) (hr : ∀ l, r l ∈ R)
    (hKE : KE (kos act M fun j => r (ι (e0 j))) d) (c : Finset κ → E) (hc : c ∈ (kos act M r).Z d) :
    c ((img e0').map ι.toEmbedding) - act N.det (c ((img e0).map ι.toEmbedding)) ∈
      sm act M (Set.range fun j => r (ι (e0 j))) := by
  have hcC : ∀ s : Finset κ, c s ∈ (if (s.card : ℤ) = (d : ℤ) then M else ⊥) := fun s =>
    (Submodule.mem_inf.1 hc).1 s (Set.mem_univ _)
  have hcD : wd (fun l => act (r l)) c = 0 := (Submodule.mem_inf.1 hc).2
  obtain ⟨m, hm⟩ : ∃ m, m = c ((img e0).map ι.toEmbedding) := ⟨_, rfl⟩
  rw [← hm]
  have hmM : m ∈ M := by
    have := hcC ((img e0).map ι.toEmbedding)
    rw [if_pos (by simp [card_img])] at this
    rwa [hm]
  have hZ0 : (fun t : Finset κ0 => c (t.map ι.toEmbedding)) ∈ (kos act M fun l => r (ι l)).Z d := by
    refine Submodule.mem_inf.2 ⟨fun s _ => ?_, ?_⟩
    · have := hcC (s.map ι.toEmbedding)
      simpa using this
    · show wd (fun l => act (r (ι l))) (fun t : Finset κ0 => c (t.map ι.toEmbedding)) = 0
      funext s
      have := (hWB κ E (fun _ => M) (fun l => act (r l))).2.2.2.2.2 κ0 ι c s
      rw [this, hcD]; rfl
  have hZ' : (fun s : Finset κ0 => act (detC ρ s) m) ∈ (kos act M fun l => r (ι l)).Z d := by
    refine Submodule.mem_inf.2 ⟨fun s _ => ?_, ?_⟩
    · show act (detC ρ s) m ∈ (if (s.card : ℤ) = (d : ℤ) then M else ⊥)
      split_ifs with hs
      · exact hSt _ (detC_mem R ρ hρ s) m hmM
      · have : s.card ≠ d := fun h => hs (by rw [h])
        simp [detC, this]
    · show wd (fun l => act (r (ι l))) (fun s : Finset κ0 => act (detC ρ s) m) = 0
      have := hDet S E act κ0 d ρ (fun b => r (ι (e0 b))) m
      rwa [show (fun l => act (∑ b, ρ l b * r (ι (e0 b)))) = fun l => act (r (ι l)) from
        funext fun l => by rw [hrel l]] at this
  have hB := hK2 S E act κ0 R M (fun l => r (ι l)) d e0 hSt (fun l => hr _) hKE _
    (Submodule.sub_mem _ hZ0 hZ') (by
      have h1' : detC ρ (img e0) = 1 := by
        rw [detC_img ρ e0 1 (fun a => by rw [h1 a]; ext b; simp [Matrix.one_apply, Pi.single_apply, eq_comm])]
        simp
      simp only [Pi.sub_apply, h1', map_one, Module.End.one_apply, ← hm, sub_self]
      exact Submodule.zero_mem _)
  have hval := (hKS S E act κ0 R M (fun l => r (ι l)) hSt (fun l => hr _)).2 d _ hB (img e0')
  have hdet : detC ρ (img e0') = N.det := detC_img ρ e0' N h2
  simp only [Pi.sub_apply, hdet] at hval
  refine (?_ : sm act M (Set.range fun l => r (ι l)) ≤ sm act M (Set.range fun j => r (ι (e0 j)))) hval
  unfold sm
  refine iSup₂_le ?_
  rintro _ ⟨l, rfl⟩ _ ⟨x, hx, rfl⟩
  show act (r (ι l)) x ∈ _
  rw [hrel l, map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [mul_comm, map_mul, Module.End.mul_apply]
  exact (le_iSup₂_of_le (f := fun (t : S) (_ : t ∈ Set.range fun j => r (ι (e0 j))) => M.map (act t))
    (r (ι (e0 b))) ⟨b, rfl⟩ le_rfl) (Submodule.mem_map_of_mem (hSt _ (hρ l b) x hx))

/- English proof (translation)
Introduce `hDet hK2 hKS hWB S E _ _ _ _ act κ _ _ R M r d e e' N hSt hr hN hrel hdis hKE c hc`. Establish `hmemL : ∀ j, e j ∈ img e ∪ img e'` using `fun j => Finset.mem_union_left _ (by simp [img])`. Establish `hmemR : ∀ j, e' j ∈ img e ∪ img e'` using `fun j => Finset.mem_union_right _ (by simp [img])`. Set `ι : {l // l ∈ img e ∪ img e'} ↪o κ` to `OrderEmbedding.subtype _`. Set `e0 : Fin d ↪o {l // l ∈ img e ∪ img e'}` to `OrderEmbedding.ofStrictMono (fun j => ⟨e j, hmemL j⟩) fun a b h => e.strictMono h`.

Set `e0' : Fin d ↪o {l // l ∈ img e ∪ img e'}` to `OrderEmbedding.ofStrictMono (fun j => ⟨e' j, hmemR j⟩) fun a b h => e'.strictMono h`. Set `ρ : {l // l ∈ img e ∪ img e'} → Fin d → S` to `fun l => if h : ∃ j, e j = l.1 then Pi.single h.choose 1 else if h' : ∃ a, e' a = l.1 then N h'.choose else 0`. Establish `h1 : ∀ j, ρ (e0 j) = Pi.single j 1` using `fun j => by`. Establish `hex : ∃ i, e i = (e0 j).1` using `⟨j, rfl⟩`. Establish `: hex.choose = j` using `e.injective hex.choose_spec`.

Simplify using `only [ρ]`. Rewrite using `[dif_pos hex, this]`. Establish `h2 : ∀ a, ρ (e0' a) = N a` using `fun a => by`. Establish `hn : ¬ ∃ j, e j = (e0' a).1` using `fun ⟨j, hj⟩ => hdis a j hj.symm`. Establish `hex : ∃ i, e' i = (e0' a).1` using `⟨a, rfl⟩`.

Establish `: hex.choose = a` using `e'.injective hex.choose_spec`. Simplify using `only [ρ]`. Rewrite using `[dif_neg hn, dif_pos hex, this]`. Establish `hρ : ∀ l b, ρ l b ∈ R` using `fun l b => by`. Simplify using `only [ρ]`.

Use `split_ifs with h h'`. Rewrite using `[Pi.single_apply] split_ifs`. Conclude with `R.one_mem`. Conclude with `R.zero_mem`. Conclude with `hN _ _`.

Conclude with `R.zero_mem`. Establish `hrel' : ∀ l, r (ι l) = ∑ b, ρ l b * r (ι (e0 b))` using `fun l => by`. Take `⟨l, hl⟩` from `l`. Break down `Finset.mem_union.1 hl with h | h` into its components or cases. Take `⟨j, -, rfl⟩` from `Finset.mem_map.1 h`.

Use `h1 j` as an intermediate fact. Express the relevant statement in the definitionally equal form `r (e j) = ∑ b, ρ (e0 j) b * r (e b)`. Rewrite using `[this]`. Simplify using `[Pi.single_apply]`. Take `⟨a, -, rfl⟩` from `Finset.mem_map.1 h`.

Use `h2 a` as an intermediate fact. Express the relevant statement in the definitionally equal form `r (e' a) = ∑ b, ρ (e0' a) b * r (e b)`. Rewrite using `[this]`. Conclude with `hrel a`. Establish `key` using `core hDet hK2 hKS hWB act R M r ι e0 e0' N ρ h1 h2 hρ hrel' hSt hr hKE c hc`.

Establish `hi : (img e0).map ι.toEmbedding = img e`. Use extensionality with `x`. Simplify using `[img, ι, e0]`. Establish `hi' : (img e0').map ι.toEmbedding = img e'`. Use extensionality with `x`.

Simplify using `[img, ι, e0']`. Rewrite `key` using `[hi, hi']`. Conclude with `key`.
-/
theorem UpperTheory.Gal.productCup_of_system.koszulThree_of_det :
    Det → KoszulBoundaryOfComponentMemIdeal → KSub → WdBasic → K3 := by
  intro hDet hK2 hKS hWB S E _ _ _ _ act κ _ _ R M r d e e' N hSt hr hN hrel hdis hKE c hc
  classical
  have hmemL : ∀ j, e j ∈ img e ∪ img e' := fun j => Finset.mem_union_left _ (by simp [img])
  have hmemR : ∀ j, e' j ∈ img e ∪ img e' := fun j => Finset.mem_union_right _ (by simp [img])
  let ι : {l // l ∈ img e ∪ img e'} ↪o κ := OrderEmbedding.subtype _
  let e0 : Fin d ↪o {l // l ∈ img e ∪ img e'} :=
    OrderEmbedding.ofStrictMono (fun j => ⟨e j, hmemL j⟩) fun a b h => e.strictMono h
  let e0' : Fin d ↪o {l // l ∈ img e ∪ img e'} :=
    OrderEmbedding.ofStrictMono (fun j => ⟨e' j, hmemR j⟩) fun a b h => e'.strictMono h
  let ρ : {l // l ∈ img e ∪ img e'} → Fin d → S := fun l =>
    if h : ∃ j, e j = l.1 then Pi.single h.choose 1 else if h' : ∃ a, e' a = l.1 then N h'.choose else 0
  have h1 : ∀ j, ρ (e0 j) = Pi.single j 1 := fun j => by
    have hex : ∃ i, e i = (e0 j).1 := ⟨j, rfl⟩
    have : hex.choose = j := e.injective hex.choose_spec
    simp only [ρ]
    rw [dif_pos hex, this]
  have h2 : ∀ a, ρ (e0' a) = N a := fun a => by
    have hn : ¬ ∃ j, e j = (e0' a).1 := fun ⟨j, hj⟩ => hdis a j hj.symm
    have hex : ∃ i, e' i = (e0' a).1 := ⟨a, rfl⟩
    have : hex.choose = a := e'.injective hex.choose_spec
    simp only [ρ]
    rw [dif_neg hn, dif_pos hex, this]
  have hρ : ∀ l b, ρ l b ∈ R := fun l b => by
    simp only [ρ]
    split_ifs with h h'
    · rw [Pi.single_apply]
      split_ifs
      · exact R.one_mem
      · exact R.zero_mem
    · exact hN _ _
    · exact R.zero_mem
  have hrel' : ∀ l, r (ι l) = ∑ b, ρ l b * r (ι (e0 b)) := fun l => by
    obtain ⟨l, hl⟩ := l
    rcases Finset.mem_union.1 hl with h | h
    · obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 h
      have := h1 j
      change r (e j) = ∑ b, ρ (e0 j) b * r (e b)
      rw [this]
      simp [Pi.single_apply]
    · obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 h
      have := h2 a
      change r (e' a) = ∑ b, ρ (e0' a) b * r (e b)
      rw [this]
      exact hrel a
  have key := core hDet hK2 hKS hWB act R M r ι e0 e0' N ρ h1 h2 hρ hrel' hSt hr hKE c hc
  have hi : (img e0).map ι.toEmbedding = img e := by
    ext x; simp [img, ι, e0]
  have hi' : (img e0').map ι.toEmbedding = img e' := by
    ext x; simp [img, ι, e0']
  rw [hi, hi'] at key
  exact key
