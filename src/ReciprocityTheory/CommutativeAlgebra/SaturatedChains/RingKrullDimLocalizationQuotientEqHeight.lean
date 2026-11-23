module

public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.LocDim

@[expose] public section

namespace ReciprocityTheory.CA

open IsLocalRing

private theorem height_eq_order_height_lemma {R : Type*} [CommRing R] (I : Ideal R)
    [hI : I.IsPrime] : I.height = Order.height (⟨I, hI⟩ : PrimeSpectrum R) := by
  exact PrimeSpectrum.height_eq_orderHeight ⟨I, hI⟩

private theorem comap_map_mk_lemma_4 {R : Type*} [CommRing R] (I J : Ideal R) (h : I ≤ J) :
    Ideal.comap (Ideal.Quotient.mk I) (J.map (Ideal.Quotient.mk I)) = J := by
  ext z
  rw [Ideal.mem_comap]
  first
  | exact Ideal.mem_quotient_iff_mem h
  | exact Ideal.mem_quotient_iff_mem_sup.trans (by rw [sup_eq_left.mpr h])

private theorem height_le_height_Iic_lemma_2 {α β : Type*} [PartialOrder α] [Preorder β] (a : α)
    (f : Set.Iic a → β) (hf : StrictMono f) : Order.height a ≤ Order.height (f ⟨a, le_rfl⟩) := by
  have hmono : ∀ s : LTSeries α, Monotone s := fun s => by
    first
    | exact s.monotone
    | exact s.strictMono.monotone
  have H : ∀ s : LTSeries α, s.last ≤ a → (s.length : ℕ∞) ≤ Order.height (f ⟨a, le_rfl⟩) := by
    intro s hs
    let t : LTSeries β :=
      { length := s.length
        toFun := fun i => f ⟨s i, (hmono s (Fin.le_last i)).trans hs⟩
        step := fun i => hf (Subtype.mk_lt_mk.mpr (s.step i)) }
    have ht : t.last ≤ f ⟨a, le_rfl⟩ := by
      show f ⟨s (Fin.last s.length), _⟩ ≤ f ⟨a, le_rfl⟩
      exact hf.monotone (show s (Fin.last s.length) ≤ a from hs)
    exact Order.length_le_height ht
  first
  | exact Order.height_le_iff.mpr fun s hs => H s hs.le
  | exact Order.height_le fun s hs => H s hs.le
  | (unfold Order.height; exact iSup₂_le fun s hs => H s hs)

private theorem krullDim_le_height_lemma_3 {α β : Type*} [Preorder α] [Preorder β] (f : α → β)
    (hf : StrictMono f) (b : β) (hb : ∀ x, f x ≤ b) :
    Order.krullDim α ≤ (Order.height b : WithBot ℕ∞) := by
  unfold Order.krullDim
  refine iSup_le fun s => ?_
  have h := Order.length_le_height (p := s.map f hf) (x := b) (hb s.last)
  exact_mod_cast h

private theorem height_le_krullDim_lemma_6 {α : Type*} [Preorder α] (a : α) :
    (Order.height a : WithBot ℕ∞) ≤ Order.krullDim α := Order.height_le_krullDim a

theorem ringKrullDim_localization_quotient_eq_height {P : Type*} [CommRing P] (p q : Ideal P)
    [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) :
    ringKrullDim (Localization.AtPrime q ⧸ p.map (algebraMap P (Localization.AtPrime q))) =
      ((q.map (Ideal.Quotient.mk p)).height : WithBot ℕ∞) := by
  haveI hQ : (q.map (Ideal.Quotient.mk p)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hpq)
  have hdisj : Disjoint (q.primeCompl : Set P) (p : Set P) :=
    Set.disjoint_left.mpr fun x hx hxp => hx (hpq hxp)
  haveI hp' : (p.map (algebraMap P (Localization.AtPrime q))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p ‹_› hdisj
  rw [height_eq_order_height_lemma (q.map (Ideal.Quotient.mk p))]
  show Order.krullDim (PrimeSpectrum (Localization.AtPrime q ⧸ p.map (algebraMap P (Localization.AtPrime q)))) = _

  have hpA : ∀ x : PrimeSpectrum (Localization.AtPrime q ⧸ p.map (algebraMap P (Localization.AtPrime q))),
      p ≤ Ideal.comap (algebraMap P (Localization.AtPrime q)) (Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q)))) x.asIdeal) := by
    intro x z hz
    rw [Ideal.mem_comap, Ideal.mem_comap,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hz)]
    exact x.asIdeal.zero_mem
  have hAq : ∀ x : PrimeSpectrum (Localization.AtPrime q ⧸ p.map (algebraMap P (Localization.AtPrime q))),
      Ideal.comap (algebraMap P (Localization.AtPrime q)) (Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q)))) x.asIdeal) ≤ q := by
    intro x z hz
    by_contra hzq
    rw [Ideal.mem_comap, Ideal.mem_comap] at hz
    exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hz
      ((IsLocalization.map_units (Localization.AtPrime q) (⟨z, hzq⟩ : q.primeCompl)).map (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q))))))
  apply le_antisymm
  · refine krullDim_le_height_lemma_3 (fun x => (⟨(Ideal.comap (algebraMap P (Localization.AtPrime q))
        (Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q)))) x.asIdeal)).map (Ideal.Quotient.mk p),
        Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
          (by rw [Ideal.mk_ker]; exact hpA x)⟩ : PrimeSpectrum (P ⧸ p))) ?_ _ ?_
    · intro x y hxy
      show (Ideal.comap (algebraMap P (Localization.AtPrime q)) (Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q)))) x.asIdeal)).map
          (Ideal.Quotient.mk p) < (Ideal.comap (algebraMap P (Localization.AtPrime q))
          (Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q)))) y.asIdeal)).map (Ideal.Quotient.mk p)
      refine lt_of_le_of_ne (Ideal.map_mono (Ideal.comap_mono (Ideal.comap_mono
        (show x.asIdeal ≤ y.asIdeal from hxy.le)))) fun e => hxy.ne ?_
      have e1 := congrArg (Ideal.comap (Ideal.Quotient.mk p)) e
      rw [comap_map_mk_lemma_4 _ _ (hpA x), comap_map_mk_lemma_4 _ _ (hpA y)] at e1
      have e2 := congrArg (Ideal.map (algebraMap P (Localization.AtPrime q))) e1
      rw [IsLocalization.map_under (M := q.primeCompl) (S := Localization.AtPrime q),
        IsLocalization.map_under (M := q.primeCompl) (S := Localization.AtPrime q)] at e2
      exact PrimeSpectrum.ext (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective e2)
    · intro x
      show _ ≤ q.map (Ideal.Quotient.mk p)
      exact Ideal.map_mono (hAq x)
  · have hpB : ∀ x : PrimeSpectrum (P ⧸ p), p ≤ Ideal.comap (Ideal.Quotient.mk p) x.asIdeal := by
      intro x z hz
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hz]
      exact x.asIdeal.zero_mem
    have hB : ∀ x : Set.Iic (⟨q.map (Ideal.Quotient.mk p), hQ⟩ : PrimeSpectrum (P ⧸ p)), Ideal.comap (Ideal.Quotient.mk p) x.1.asIdeal ≤ q := fun x =>
      (Ideal.comap_mono (show x.1.asIdeal ≤ q.map (Ideal.Quotient.mk p) from x.2)).trans
        (comap_map_mk_lemma_4 p q hpq).le
    have hdB : ∀ x : Set.Iic (⟨q.map (Ideal.Quotient.mk p), hQ⟩ : PrimeSpectrum (P ⧸ p)), Disjoint (q.primeCompl : Set P)
        (Ideal.comap (Ideal.Quotient.mk p) x.1.asIdeal : Set P) := fun x =>
      Set.disjoint_left.mpr fun z hz hzB => hz (hB x hzB)
    have hBprime : ∀ x : Set.Iic (⟨q.map (Ideal.Quotient.mk p), hQ⟩ : PrimeSpectrum (P ⧸ p)),
        ((Ideal.comap (Ideal.Quotient.mk p) x.1.asIdeal).map (algebraMap P (Localization.AtPrime q))).IsPrime :=
      fun x => IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ _ inferInstance (hdB x)
    have hCprime : ∀ x : Set.Iic (⟨q.map (Ideal.Quotient.mk p), hQ⟩ : PrimeSpectrum (P ⧸ p)), (((Ideal.comap (Ideal.Quotient.mk p) x.1.asIdeal).map
        (algebraMap P (Localization.AtPrime q))).map (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q))))).IsPrime := by
      intro x
      haveI := hBprime x
      exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact Ideal.map_mono (hpB x.1))
    let h : Set.Iic (⟨q.map (Ideal.Quotient.mk p), hQ⟩ : PrimeSpectrum (P ⧸ p)) → PrimeSpectrum (Localization.AtPrime q ⧸ p.map (algebraMap P (Localization.AtPrime q))) := fun x => ⟨_, hCprime x⟩
    have hh : StrictMono h := by
      intro x y hxy
      show ((Ideal.comap (Ideal.Quotient.mk p) x.1.asIdeal).map (algebraMap P (Localization.AtPrime q))).map
          (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q)))) < ((Ideal.comap (Ideal.Quotient.mk p) y.1.asIdeal).map
          (algebraMap P (Localization.AtPrime q))).map (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q))))
      refine lt_of_le_of_ne (Ideal.map_mono (Ideal.map_mono (Ideal.comap_mono
        (show x.1.asIdeal ≤ y.1.asIdeal from hxy.le)))) fun e => hxy.ne ?_
      have e1 := congrArg (Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q))))) e
      rw [comap_map_mk_lemma_4 _ _ (Ideal.map_mono (hpB x.1)),
        comap_map_mk_lemma_4 _ _ (Ideal.map_mono (hpB y.1))] at e1
      have e2 := congrArg (Ideal.under P) e1
      rw [IsLocalization.under_map_of_isPrime_disjoint (M := q.primeCompl) (S := Localization.AtPrime q)
          inferInstance (hdB x),
        IsLocalization.under_map_of_isPrime_disjoint (M := q.primeCompl) (S := Localization.AtPrime q)
          inferInstance (hdB y)] at e2
      exact Subtype.ext (PrimeSpectrum.ext
        (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective e2))
    calc ((Order.height (⟨q.map (Ideal.Quotient.mk p), hQ⟩ : PrimeSpectrum (P ⧸ p)) : ℕ∞) :
          WithBot ℕ∞)
        ≤ (Order.height (h ⟨⟨q.map (Ideal.Quotient.mk p), hQ⟩, Set.mem_Iic.mpr le_rfl⟩) :
          WithBot ℕ∞) :=
          WithBot.coe_le_coe.mpr (height_le_height_Iic_lemma_2 _ h hh)
      _ ≤ Order.krullDim (PrimeSpectrum (Localization.AtPrime q ⧸ p.map (algebraMap P (Localization.AtPrime q)))) := height_le_krullDim_lemma_6 _

private theorem height_map_atPrime_lemma_5 {R : Type*} [CommRing R] (p q : Ideal R) [p.IsPrime]
    [q.IsPrime] (hpq : p ≤ q) [hp' : (p.map (algebraMap R (Localization.AtPrime q))).IsPrime] :
    (p.map (algebraMap R (Localization.AtPrime q))).height = p.height := by
  have hdisj : ∀ I : Ideal R, I ≤ q → Disjoint (q.primeCompl : Set R) (I : Set R) := fun I hI =>
    Set.disjoint_left.mpr fun x hx hxI => hx (hI hxI)
  rw [height_eq_order_height_lemma (p.map (algebraMap R (Localization.AtPrime q))),
    height_eq_order_height_lemma p]
  apply le_antisymm
  · let f : PrimeSpectrum (Localization.AtPrime q) → PrimeSpectrum R := fun x =>
      ⟨Ideal.comap (algebraMap R (Localization.AtPrime q)) x.asIdeal, inferInstance⟩
    have hf : StrictMono f := by
      intro x y hxy
      show Ideal.comap (algebraMap R (Localization.AtPrime q)) x.asIdeal <
        Ideal.comap (algebraMap R (Localization.AtPrime q)) y.asIdeal
      refine lt_of_le_of_ne (Ideal.comap_mono (show x.asIdeal ≤ y.asIdeal from hxy.le))
        fun e => hxy.ne ?_
      have e2 := congrArg (Ideal.map (algebraMap R (Localization.AtPrime q))) e
      rw [IsLocalization.map_under (M := q.primeCompl) (S := Localization.AtPrime q),
        IsLocalization.map_under (M := q.primeCompl) (S := Localization.AtPrime q)] at e2
      exact PrimeSpectrum.ext e2
    have hfp : f ⟨_, hp'⟩ = ⟨p, ‹p.IsPrime›⟩ := PrimeSpectrum.ext (by
      show Ideal.under R (p.map (algebraMap R (Localization.AtPrime q))) = p
      exact IsLocalization.under_map_of_isPrime_disjoint (M := q.primeCompl)
        (S := Localization.AtPrime q) ‹p.IsPrime› (hdisj p hpq))
    have h := Order.height_le_height_apply_of_strictMono f hf ⟨_, hp'⟩
    rwa [hfp] at h
  · let g : Set.Iic (⟨p, ‹p.IsPrime›⟩ : PrimeSpectrum R) → PrimeSpectrum (Localization.AtPrime q) :=
      fun x => ⟨x.1.asIdeal.map (algebraMap R (Localization.AtPrime q)),
        IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ _ inferInstance
          (hdisj _ ((show x.1.asIdeal ≤ p from x.2).trans hpq))⟩
    have hg : StrictMono g := by
      intro x y hxy
      show x.1.asIdeal.map (algebraMap R (Localization.AtPrime q)) <
        y.1.asIdeal.map (algebraMap R (Localization.AtPrime q))
      refine lt_of_le_of_ne (Ideal.map_mono (show x.1.asIdeal ≤ y.1.asIdeal from hxy.le))
        fun e => hxy.ne ?_
      have e2 := congrArg (Ideal.under R) e
      rw [IsLocalization.under_map_of_isPrime_disjoint (M := q.primeCompl)
          (S := Localization.AtPrime q) inferInstance
          (hdisj _ ((show x.1.asIdeal ≤ p from x.2).trans hpq)),
        IsLocalization.under_map_of_isPrime_disjoint (M := q.primeCompl)
          (S := Localization.AtPrime q) inferInstance
          (hdisj _ ((show y.1.asIdeal ≤ p from y.2).trans hpq))] at e2
      exact Subtype.ext (PrimeSpectrum.ext e2)
    exact height_le_height_Iic_lemma_2 _ g hg

theorem IsCM.height_eq_height_add_height_map_quotient {P : Type*} [CommRing P] [IsLocalRing P]
    (h : IsCM P) (p q : Ideal P) [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) :
    q.height = p.height + (q.map (Ideal.Quotient.mk p)).height := by
  have hL := h.localization_atPrime q
  have hdisj : Disjoint (q.primeCompl : Set P) (p : Set P) :=
    Set.disjoint_left.mpr fun x hx hxp => hx (hpq hxp)
  haveI hp' : (p.map (algebraMap P (Localization.AtPrime q))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p ‹_› hdisj
  have e := hL.height_add_ringKrullDim_quotient (p.map (algebraMap P (Localization.AtPrime q)))
  have e1 : (p.map (algebraMap P (Localization.AtPrime q))).height = p.height :=
    height_map_atPrime_lemma_5 p q hpq
  have e2 : ringKrullDim (Localization.AtPrime q) = q.height := by
    first
    | exact IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)
    | (haveI hqL : (q.map (algebraMap P (Localization.AtPrime q))).IsPrime :=
         IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ q ‹_›
           (Set.disjoint_left.mpr fun x hx hxq => hx hxq)
       rw [← height_map_atPrime_lemma_5 q q le_rfl,
         height_eq_order_height_lemma (q.map (algebraMap P (Localization.AtPrime q)))]
       apply le_antisymm
       · refine krullDim_le_height_lemma_3 id strictMono_id _ fun x => ?_
         show x.asIdeal ≤ q.map (algebraMap P (Localization.AtPrime q))
         rw [← IsLocalization.map_comap (M := q.primeCompl) (S := Localization.AtPrime q)
           x.asIdeal]
         refine Ideal.map_mono fun z hz => ?_
         by_contra hzq
         exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_comap.mp hz)
           (IsLocalization.map_units (Localization.AtPrime q) (⟨z, hzq⟩ : q.primeCompl)))
       · exact height_le_krullDim_lemma_6 _)
  rw [ringKrullDim_localization_quotient_eq_height p q hpq, e1, e2] at e
  exact_mod_cast e.symm

end ReciprocityTheory.CA
