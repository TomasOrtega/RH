import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

/- English proof (translation)
Use extensionality with `z`. Simplify using `only [uni, inlE, Finset.disjSum_empty, Finset.map_map, Finset.mem_map]`. Simplify using the standard rewrite rules.
-/
private lemma uni_empty_eq {α β : Type} [LinearOrder α] [LinearOrder β] (L : Finset α) :
    uni L (∅ : Finset β) = L.map (inlE : α ↪o α ⊕ₗ β).toEmbedding := by
  ext z
  simp only [uni, inlE, Finset.disjSum_empty, Finset.map_map, Finset.mem_map]
  simp

/- English proof (translation)
Use extensionality with `t`. Simplify using `[lft, uni]`.
-/
private lemma lft_uni' {α β : Type} [LinearOrder α] [LinearOrder β] (I : Finset α) (J : Finset β) :
    lft (uni I J) = I := by
  ext t
  simp [lft, uni]

/- English proof (translation)
Use extensionality with `t`. Simplify using `[rgt, uni]`.
-/
private lemma rgt_uni' {α β : Type} [LinearOrder α] [LinearOrder β] (I : Finset α) (J : Finset β) :
    rgt (uni I J) = J := by
  ext t
  simp [rgt, uni]

/- English proof (translation)
Rewrite using `[uni_empty_eq]`. Use extensionality with `t`. Simplify using `[img]`.
-/
private lemma img_trans_inlE {d : ℕ} {α β : Type} [LinearOrder α] [LinearOrder β] (e : Fin d ↪o α) :
    img (e.trans (inlE : α ↪o α ⊕ₗ β)) = uni (img e) (∅ : Finset β) := by
  rw [uni_empty_eq]
  ext t
  simp [img]

/- English proof (translation)
Simplify using `[img]`.
-/
private lemma img_card {d : ℕ} {α : Type} [LinearOrder α] (e : Fin d ↪o α) : (img e).card = d := by
  simp [img]

/- English proof (translation)
Introduce `hZCol hColZ hSysL2 hK2 hKSub hRS hActsLin hSysOk hGoodZ hThMu`. Introduce `F K _ _ _ _ _ _ d x hcov τ htop a ha κ _ _ n z hz`. Establish `hGood : (sysZ K x a).Good` using `(hGoodZ F K d x hcov a).1`. Establish `hAdm : (sysZ K x a).admitted (app n11 n) (app (sysZ K x a).mu z)`. Introduce `i j l`.

Take `⟨l, rfl⟩ : ∃ l', toLex l' = l` from `⟨ofLex l, rfl⟩`. Consider the cases of `l with`. Consider the case `inl m => exact (hThMu d _ _ (sysZ K x a) hGood).1 i j m`. Consider the case `inr k => exact hz.adm i j k`. Establish `gen : ∀ (T : Sys d (K ⊗[ℂ] K) (DR ℂ K ⊗[ℂ] DR ℂ K)) (i j : Fin (d + 1)), (fun l => T.r (app n11 n) (app T.mu z) i j (((dj j).trans (inlE (κ` using `κ))) l)) = fun l => T.r n11 T.mu i j (dj j l) := fun T i j => rfl`.

Establish `hOk` using `hSysOk d _ _ (sysZ K x a) _ (app n11 n) (app (sysZ K x a).mu z) hGood hAdm`. Establish `key : ∀ (I J : Finset (Fin (d + 1))) (i j : Fin (d + 1)), i ∈ I → j ∈ J → ∀ D ∈ ((sysZ K x a).colCx (app n11 n) (app (sysZ K x a).mu z) I J).Z d, Acts (F` using `F) K τ a (D (uni (img (dj j)) ∅)) 0 → D ∈ ((sysZ K x a).colCx (app n11 n) (app (sysZ K x a).mu z) I J).B d := by`. Introduce `I J i j hi hj D hD hA`. Establish `hI : I.Nonempty` using `⟨i, hi⟩`. Establish `hJ : J.Nonempty` using `⟨j, hj⟩`.

Take `⟨hr, hcol⟩` from `hOk.2.1 I J i hi j hj`. Rewrite `hD`, the goal using `[hcol]`. Establish `hR` using `hRS _ _ (sysZ K x a).act _ ((sysZ K x a).M I J) ((sysZ K x a).u (app n11 n) i j) ((sysZ K x a).r (app n11 n) (app (sysZ K x a).mu z) i j) (app (sysZ K x a).mu z) (fun l => rfl) d D`. Rewrite using `[hR.2.2.1]`. Rewrite `hD` using `[hR.2.1]`.

Establish `hCZ` using `hColZ F K d x hcov τ htop a ha I J i hi j hj`. Use `hK2 _ _ (sysZ K x a).act _ ((sysZ K x a).R I J) ((sysZ K x a).M I J) _ d ((dj j).trans inlE) (hGood.stab I J hI hJ) hr (by rw [gen]; exact hCZ.1) _ hD ?_` and prove the remaining obligations. Rewrite using `[img_trans_inlE, gen]`. Use `hCZ.2 _ ?_ ?_` and prove the remaining obligations. Establish `hC` using `(Submodule.mem_inf.1 hD).1`.

Simplify using `only [kos, acx] at hC`. Establish `h1` using `(Submodule.mem_pi.1 hC) (uni (img (dj j)) ∅) (Set.mem_univ _)`. Establish `hcard : (uni (img (dj j)) (∅ : Finset κ)).card = d`. Rewrite using `[← img_trans_inlE, img_card]`. Rewrite `h1` using `[hcard, if_pos rfl]`.

Conclude with `h1`. Establish `h2` using `fun s => (hActsLin F K d x hcov τ htop a).2.1 _ 0 s hA`. Simplify using `only [mul_zero] at h2`. Conclude with `h2 _`. Establish `hKE : ∀ I J : Finset (Fin (d + 1)), I.Nonempty → J.Nonempty → KE ((sysZ K x a).colCx (app n11 n) (app (sysZ K x a).mu z) I J) d`.

Introduce `I J hI hJ`. Take `⟨i, hi⟩` from `hI`. Take `⟨j, hj⟩` from `hJ`. Take `⟨hr, hcol⟩` from `hOk.2.1 I J i hi j hj`. Rewrite using `[hcol]`.

Establish `hks` using `(hKSub _ _ (sysZ K x a).act _ ((sysZ K x a).R I J) ((sysZ K x a).M I J) ((sysZ K x a).r (app n11 n) (app (sysZ K x a).mu z) i j) (hGood.stab I J ⟨i, hi⟩ ⟨j, hj⟩) hr).1 d ((dj j).trans inlE) (by rw [gen]; exact (hColZ F K d x hcov τ htop a ha I J i hi j hj).1)`. Introduce `m hm c hc`. Establish `hR` using `hRS _ _ (sysZ K x a).act _ ((sysZ K x a).M I J) ((sysZ K x a).u (app n11 n) i j) ((sysZ K x a).r (app n11 n) (app (sysZ K x a).mu z) i j) (app (sysZ K x a).mu z) (fun l => rfl) m c`. Rewrite using `[hR.2.2.1]`. Conclude with `hks m hm (hR.2.1.1 hc)`.

Establish `hc0` using `fun i j => hZCol F K d x hcov τ htop a ha κ n z hz i j`. Use `choose c0 hc0Z hc0A using hc0`. Establish `hAct` using `(hActsLin F K d x hcov τ htop a).1`. Take `⟨c, hcZ, hcol⟩` from `hSysL2 d _ _ (sysZ K x a) _ (app n11 n) (app (sysZ K x a).mu z) hGood hAdm hKE c0 hc0Z (fun i i' j => by`. Apply `key {i, i'} {j} i j (by simp) (by simp)` to reduce the goal to its premises.

Conclude with `Submodule.sub_mem _ (hOk.2.2 {i} {i, i'} {j} {j} (by simp) (by simp) (by simp) le_rfl d (hc0Z i j)) (hOk.2.2 {i'} {i, i'} {j} {j} (by simp) (by simp) (by simp) le_rfl d (hc0Z i' j))`. Establish `h3` using `(hAct _ _ _ _ (hc0A i j _ (img_card (dj j))) (hc0A i' j _ (img_card (dj j)))).2`. Rewrite `h3` using `[sub_self]`. Conclude with `h3)`. Use the proof step `(fun i j j' => by`.

Apply `key {i} {j, j'} i j (by simp) (by simp)` to reduce the goal to its premises. Conclude with `Submodule.sub_mem _ (hOk.2.2 {i} {i} {j} {j, j'} (by simp) (by simp) le_rfl (by simp) d (hc0Z i j)) (hOk.2.2 {i} {i} {j'} {j, j'} (by simp) (by simp) le_rfl (by simp) d (hc0Z i j'))`. Establish `h3` using `(hAct _ _ _ _ (hc0A i j _ (img_card (dj j))) (hc0A i j' _ (img_card (dj j)))).2`. Rewrite `h3` using `[sub_self]`. Conclude with `h3)`.

Use `⟨c, hcZ, ?_⟩` and prove the remaining obligations. Introduce `i j L hLc`. Establish `e : resK inlE c (uni (uni {i} {j}) L) = c0 i j (uni L ∅)`. Rewrite using `[← hcol i j]`. Simplify using `only [resK, col, lft_uni', rgt_uni', uni_empty_eq]`.

Rewrite using `[e]`. Conclude with `hc0A i j L hLc`.
-/
theorem UpperTheory.Gal.productCup_of_system.zEx_of :
    ZCol → ColZ → CechKoszulSystemCocycleGluing → KoszulBoundaryOfComponentMemIdeal → KSub → RS → ActsLin → SysOk → GoodZ → ThMuLat → ZEx := by
  intro hZCol hColZ hSysL2 hK2 hKSub hRS hActsLin hSysOk hGoodZ hThMu
  intro F K _ _ _ _ _ _ d x hcov τ htop a ha κ _ _ n z hz
  have hGood : (sysZ K x a).Good := (hGoodZ F K d x hcov a).1
  have hAdm : (sysZ K x a).admitted (app n11 n) (app (sysZ K x a).mu z) := by
    intro i j l
    obtain ⟨l, rfl⟩ : ∃ l', toLex l' = l := ⟨ofLex l, rfl⟩
    cases l with
    | inl m => exact (hThMu d _ _ (sysZ K x a) hGood).1 i j m
    | inr k => exact hz.adm i j k
  have gen : ∀ (T : Sys d (K ⊗[ℂ] K) (DR ℂ K ⊗[ℂ] DR ℂ K)) (i j : Fin (d + 1)),
      (fun l => T.r (app n11 n) (app T.mu z) i j (((dj j).trans (inlE (κ := κ))) l)) =
        fun l => T.r n11 T.mu i j (dj j l) := fun T i j => rfl
  have hOk := hSysOk d _ _ (sysZ K x a) _ (app n11 n) (app (sysZ K x a).mu z) hGood hAdm
  have key : ∀ (I J : Finset (Fin (d + 1))) (i j : Fin (d + 1)), i ∈ I → j ∈ J →
      ∀ D ∈ ((sysZ K x a).colCx (app n11 n) (app (sysZ K x a).mu z) I J).Z d,
      Acts (F := F) K τ a (D (uni (img (dj j)) ∅)) 0 →
      D ∈ ((sysZ K x a).colCx (app n11 n) (app (sysZ K x a).mu z) I J).B d := by
    intro I J i j hi hj D hD hA
    have hI : I.Nonempty := ⟨i, hi⟩
    have hJ : J.Nonempty := ⟨j, hj⟩
    obtain ⟨hr, hcol⟩ := hOk.2.1 I J i hi j hj
    rw [hcol] at hD ⊢
    have hR := hRS _ _ (sysZ K x a).act _ ((sysZ K x a).M I J) ((sysZ K x a).u (app n11 n) i j)
      ((sysZ K x a).r (app n11 n) (app (sysZ K x a).mu z) i j) (app (sysZ K x a).mu z) (fun l => rfl) d D
    rw [hR.2.2.1]
    rw [hR.2.1] at hD
    have hCZ := hColZ F K d x hcov τ htop a ha I J i hi j hj
    refine hK2 _ _ (sysZ K x a).act _ ((sysZ K x a).R I J) ((sysZ K x a).M I J) _ d ((dj j).trans inlE)
      (hGood.stab I J hI hJ) hr (by rw [gen]; exact hCZ.1) _ hD ?_
    rw [img_trans_inlE, gen]
    refine hCZ.2 _ ?_ ?_
    · have hC := (Submodule.mem_inf.1 hD).1
      simp only [kos, acx] at hC
      have h1 := (Submodule.mem_pi.1 hC) (uni (img (dj j)) ∅) (Set.mem_univ _)
      have hcard : (uni (img (dj j)) (∅ : Finset κ)).card = d := by
        rw [← img_trans_inlE, img_card]
      rw [hcard, if_pos rfl] at h1
      exact h1
    · have h2 := fun s => (hActsLin F K d x hcov τ htop a).2.1 _ 0 s hA
      simp only [mul_zero] at h2
      exact h2 _
  have hKE : ∀ I J : Finset (Fin (d + 1)), I.Nonempty → J.Nonempty →
      KE ((sysZ K x a).colCx (app n11 n) (app (sysZ K x a).mu z) I J) d := by
    intro I J hI hJ
    obtain ⟨i, hi⟩ := hI
    obtain ⟨j, hj⟩ := hJ
    obtain ⟨hr, hcol⟩ := hOk.2.1 I J i hi j hj
    rw [hcol]
    have hks := (hKSub _ _ (sysZ K x a).act _ ((sysZ K x a).R I J) ((sysZ K x a).M I J)
      ((sysZ K x a).r (app n11 n) (app (sysZ K x a).mu z) i j) (hGood.stab I J ⟨i, hi⟩ ⟨j, hj⟩) hr).1 d
      ((dj j).trans inlE) (by rw [gen]; exact (hColZ F K d x hcov τ htop a ha I J i hi j hj).1)
    intro m hm c hc
    have hR := hRS _ _ (sysZ K x a).act _ ((sysZ K x a).M I J) ((sysZ K x a).u (app n11 n) i j)
      ((sysZ K x a).r (app n11 n) (app (sysZ K x a).mu z) i j) (app (sysZ K x a).mu z) (fun l => rfl) m c
    rw [hR.2.2.1]
    exact hks m hm (hR.2.1.1 hc)
  have hc0 := fun i j => hZCol F K d x hcov τ htop a ha κ n z hz i j
  choose c0 hc0Z hc0A using hc0
  have hAct := (hActsLin F K d x hcov τ htop a).1
  obtain ⟨c, hcZ, hcol⟩ := hSysL2 d _ _ (sysZ K x a) _ (app n11 n) (app (sysZ K x a).mu z) hGood hAdm hKE c0 hc0Z
    (fun i i' j => by
      apply key {i, i'} {j} i j (by simp) (by simp)
      · exact Submodule.sub_mem _
          (hOk.2.2 {i} {i, i'} {j} {j} (by simp) (by simp) (by simp) le_rfl d (hc0Z i j))
          (hOk.2.2 {i'} {i, i'} {j} {j} (by simp) (by simp) (by simp) le_rfl d (hc0Z i' j))
      · have h3 := (hAct _ _ _ _ (hc0A i j _ (img_card (dj j))) (hc0A i' j _ (img_card (dj j)))).2
        rw [sub_self] at h3
        exact h3)
    (fun i j j' => by
      apply key {i} {j, j'} i j (by simp) (by simp)
      · exact Submodule.sub_mem _
          (hOk.2.2 {i} {i} {j} {j, j'} (by simp) (by simp) le_rfl (by simp) d (hc0Z i j))
          (hOk.2.2 {i} {i} {j'} {j, j'} (by simp) (by simp) le_rfl (by simp) d (hc0Z i j'))
      · have h3 := (hAct _ _ _ _ (hc0A i j _ (img_card (dj j))) (hc0A i j' _ (img_card (dj j)))).2
        rw [sub_self] at h3
        exact h3)
  refine ⟨c, hcZ, ?_⟩
  intro i j L hLc
  have e : resK inlE c (uni (uni {i} {j}) L) = c0 i j (uni L ∅) := by
    rw [← hcol i j]
    simp only [resK, col, lft_uni', rgt_uni', uni_empty_eq]
  rw [e]
  exact hc0A i j L hLc
