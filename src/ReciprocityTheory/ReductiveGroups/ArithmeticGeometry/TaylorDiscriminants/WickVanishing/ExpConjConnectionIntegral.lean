module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SigCancel

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

section Lift

variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ}

theorem liftX_one : liftX k (1 : PS k 1 d) = 1 := by
  rw [liftX, ← MvPowerSeries.coe_substAlgHom (liftX_hs k), map_one]

theorem liftX_add (f g : PS k 1 d) : liftX k (f + g) = liftX k f + liftX k g := by
  rw [liftX, liftX, liftX, ← MvPowerSeries.coe_substAlgHom (liftX_hs k), map_add (f := _)]

theorem liftX_sub (f g : PS k 1 d) : liftX k (f - g) = liftX k f - liftX k g := by
  rw [liftX, liftX, liftX, ← MvPowerSeries.coe_substAlgHom (liftX_hs k), map_sub]

theorem liftX_C (a : k) : liftX k (C a : PS k 1 d) = C a := by
  have h1 : (C a : PS k 1 d) = algebraMap k (PS k 1 d) a := by
    rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have h2 : (C a : AA k d) = algebraMap k (AA k d) a := by
    rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [h1, h2, liftX, ← MvPowerSeries.coe_substAlgHom (liftX_hs k), AlgHom.commutes]

end Lift

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem ig_FK (B : FB R d O) (j : Fin d) : B.FK k j ∈ Ig R k (Fin 2 × Fin d) := by
  simp only [FB.FK, FGLaw.mapF]
  exact ig_map _

theorem exp_conj_connection_integral {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) (w0 : O) (hw : w0 + star w0 = 1)
    (m : ℕ) (u' φ' : Fin d → R) (G : AA k d) (hG : G ∈ Ig R k (Fin d ⊕ Fin d)) :
    liftX k (FB.expS k (-((m : k) • B.hL k h w0))) *
      nabla k B h m (fun i => algebraMap R k (u' i))
        (fun i => algebraMap R k (φ' i) - (sg1 k h).mulVec (fun j => algebraMap R k (u' j)) i)
        (liftX k (FB.expS k ((m : k) • B.hL k h w0)) * G) ∈ Ig R k (Fin d ⊕ Fin d) := by
  have cPA : CZ (![pt k (n := 1) d 0, B.actK k w0] : Fin 2 → Pt k 1 d) :=
    CZ.cons (_root_.ReciprocityTheory.ChartRestriction.G.TB.LogPf.cc_pt 0) (CZ.cons (const_actK' B w0) CZ.nil)
  have ccf : constantCoeff ((m : k) • B.hL k h w0) = 0 := by
    rw [nt_const_smul, hL_eq, cc_ev' cPA, cc_h hc, mul_zero]
  have ccf' : constantCoeff (-((m : k) • B.hL k h w0)) = 0 := by rw [map_neg, ccf, neg_zero]
  have hinv : liftX k (FB.expS k (-((m : k) • B.hL k h w0))) * liftX k (FB.expS k ((m : k) • B.hL k h w0)) = 1 := by
    rw [← liftX_mul, ← gt_expS_add _ _ ccf' ccf, neg_add_cancel, nt_expS_zero, liftX_one]
  have ig_pderiv {σ : Type} {f : MvPowerSeries σ k} (hf : f ∈ Ig R k σ) (v : σ) :
      pderiv (R := k) v f ∈ Ig R k σ := by
    obtain ⟨g, rfl⟩ := RingHom.mem_range.mp hf
    refine RingHom.mem_range.mpr ⟨pderiv (R := R) v g, ?_⟩
    ext n
    rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_pderiv,
      MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_map]
    rw [map_mul, map_add (f := _), map_one, map_natCast]
  let vf (c : (Fin d ⊕ Fin d) → AA k d) (G : AA k d) : AA k d :=
    ∑ t, c t * pderiv (R := k) t G

  have vf_mul (c : (Fin d ⊕ Fin d) → MvPowerSeries (Fin d ⊕ Fin d) k) (f G : MvPowerSeries (Fin d ⊕ Fin d) k) :
      vf c (f * G) = vf c f * G + f * vf c G := by
    simp only [vf, Derivation.leibniz, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring


  have pderiv_inl_liftX (f : PS k 1 d) (j : Fin d) :
      pderiv (R := k) (Sum.inl j) (liftX k f) = liftX k (pderiv (R := k) ((0 : Fin 1), j) f) := by
    classical
    let e : (Fin 1 × Fin d) ↪ (Fin d ⊕ Fin d) :=
      ⟨fun p => Sum.inl p.2, fun _ _ h => Prod.ext (Subsingleton.elim _ _) (Sum.inl.inj h)⟩
    have hlift (g : PS k 1 d) : liftX k g = rename e g :=
      (MvPowerSeries.rename_eq_subst e g).symm
    simp only [hlift]
    ext n
    rw [MvPowerSeries.coeff_pderiv]
    by_cases hn : n ∈ Set.range (Finsupp.embDomain e)
    · obtain ⟨m, rfl⟩ := hn
      change coeff (Finsupp.embDomain e m + Finsupp.single (e (0, j)) 1) (rename e f) *
        (Finsupp.embDomain e m (e (0, j)) + 1) =
          coeff (Finsupp.embDomain e m) (rename e (pderiv (0, j) f))
      rw [← Finsupp.embDomain_single, ← Finsupp.embDomain_add,
        MvPowerSeries.coeff_embDomain_rename, Finsupp.embDomain_apply_self,
        MvPowerSeries.coeff_embDomain_rename, MvPowerSeries.coeff_pderiv]
    · have hshift : n + Finsupp.single (Sum.inl j) 1 ∉ Set.range (Finsupp.embDomain e) :=
        fun h => hn (Finsupp.isLowerSet_range_embDomain e (le_iff_exists_add.mpr ⟨_, rfl⟩) h)
      have he : Finsupp.embDomain e = (Finsupp.mapDomain e : (Fin 1 × Fin d →₀ ℕ) → _) :=
        funext (Finsupp.embDomain_eq_mapDomain e)
      rw [he] at hn hshift
      rw [MvPowerSeries.coeff_rename_eq_zero e f hshift, zero_mul,
        MvPowerSeries.coeff_rename_eq_zero e _ hn]

  have pderiv_inr_liftX (f : PS k 1 d) (i : Fin d) :
      pderiv (R := k) (Sum.inr i) (liftX k f) = 0 := by
    classical
    let e : (Fin 1 × Fin d) ↪ (Fin d ⊕ Fin d) :=
      ⟨fun p => Sum.inl p.2, fun _ _ h => Prod.ext (Subsingleton.elim _ _) (Sum.inl.inj h)⟩
    have hlift : liftX k f = rename e f := (MvPowerSeries.rename_eq_subst e f).symm
    rw [hlift]
    ext n
    have hshift : n + Finsupp.single (Sum.inr i) 1 ∉ Set.range (Finsupp.mapDomain e) := by
      rintro ⟨m, hm⟩
      have hzero : Finsupp.embDomain e m (Sum.inr i) = 0 := by
        apply Finsupp.embDomain_of_notMem_range
        rintro ⟨p, hp⟩
        exact Sum.inl_ne_inr hp
      rw [Finsupp.embDomain_eq_mapDomain, hm] at hzero
      simp at hzero
    rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_rename_eq_zero e f hshift, zero_mul, map_zero]

  let cf (B : FB R d O) (h : PS k 2 d) (u φ : Fin d → k) : Fin d ⊕ Fin d → AA k d :=
    Sum.elim (fun j => liftX k (∑ i : Fin d, C (u i) * ev (n := 1) ![pt k d 0, 0]
      (pderiv (R := k) ((1 : Fin 2), i) (B.FK k j))))
      (fun i => liftX k (Dof (B.FK k) u (sgOf k h i)) + C (φ i))


  have cf_inl (B : FB R d O) (h : PS k 2 d) (u φ : Fin d → k) (j : Fin d) :
      cf B h u φ (Sum.inl j) =
        liftX k (∑ i : Fin d, C (u i) * ev (n := 1) ![pt k d 0, 0]
          (pderiv (R := k) ((1 : Fin 2), i) (B.FK k j))) := rfl

  have cf_inr (B : FB R d O) (h : PS k 2 d) (u φ : Fin d → k) (i : Fin d) :
      cf B h u φ (Sum.inr i) = liftX k (Dof (B.FK k) u (sgOf k h i)) + C (φ i) := rfl

  have nabla_eq (B : FB R d O) (h : PS k 2 d) (m : ℕ) (u φ : Fin d → k) (G : AA k d) :
      nabla k B h m u φ G = vf (cf B h u φ) G - (C (m : k) * fm k h u) * G := by
    unfold nabla vf fm Dx
    rw [Fintype.sum_sum_type]
    simp only [cf_inl, cf_inr, add_mul, Finset.sum_add_distrib]
    ring

  have vf_cf_liftX (B : FB R d O) (h : PS k 2 d) (u φ : Fin d → k) (g : PS k 1 d) :
      vf (cf B h u φ) (liftX k g) = liftX k (Dof (B.FK k) u g) := by
    unfold vf
    rw [Fintype.sum_sum_type]
    simp only [cf_inl, pderiv_inl_liftX, pderiv_inr_liftX, mul_zero, Finset.sum_const_zero, add_zero]
    unfold Dof
    rw [liftX_sum]
    simp only [liftX_mul]
  rw [nabla_eq, vf_mul, vf_cf_liftX, dof_expS _ _ ccf, liftX_mul]
  have e : ∀ (a b x y z : AA k d), a * (b * x * G + b * y - z * (b * G)) = (a * b) * (x * G + y - z * G) :=
    fun a b x y z => by ring
  rw [e, hinv, one_mul, smul_eq_C_mul, dof_Cmul, liftX_mul, liftX_C]
  have hfm : fm k h (fun i => algebraMap R k (u' i)) =
      ∑ i, X (Sum.inr i) * C (algebraMap R k (u' i)) - liftX k (∑ i, sgOf k h i * C (algebraMap R k (u' i))) := by
    simp only [fm, sub_mul, Finset.sum_sub_distrib, liftX_sum, liftX_mul, liftX_C]
  rw [hfm]
  have e2 : ∀ (cm D S XC y : AA k d), cm * D * G + y - cm * (XC - S) * G = y + cm * (D + S - XC) * G :=
    fun cm D S XC y => by ring
  rw [e2, ← liftX_add]
  have hm : (C ((m : ℕ) : k) : AA k d) ∈ Ig R k (Fin d ⊕ Fin d) := by
    rw [← map_natCast (algebraMap R k) m]
    exact ig_C _
  refine add_mem ?_ (mul_mem (mul_mem hm (sub_mem (ig_liftX (rel_hL hc w0 hw _ fun j => ⟨u' j, rfl⟩)) ?_)) hG)
  · simp only [vf]
    refine sum_mem fun t _ => mul_mem ?_ (ig_pderiv hG t)
    rcases t with j | i
    · rw [cf_inl]
      exact ig_liftX (sum_mem fun i _ => mul_mem (ig_C _) (ig_ev cz1 integral_family_point_zero (ig_pderiv (ig_FK B j) _)))
    · have e3 : cf B h (fun i => algebraMap R k (u' i))
          (fun i => algebraMap R k (φ' i) - (sg1 k h).mulVec (fun j => algebraMap R k (u' j)) i) (Sum.inr i) =
          liftX k (Dof (B.FK k) (fun j => algebraMap R k (u' j)) (sgOf k h i) -
            C (∑ j, sg1 k h i j * algebraMap R k (u' j))) + C (algebraMap R k (φ' i)) := by
        rw [cf_inr, liftX_sub, liftX_C]
        simp only [Matrix.mulVec, dotProduct, map_sub]
        ring
      rw [e3]
      exact add_mem (ig_liftX (dof_sig hc u' i)) (ig_C _)
  · exact sum_mem fun i _ => mul_mem (ig_X _) (ig_C _)

theorem connection_first_identity : ConnectionIntegrality := by
  intro R _ d O _ _ k _ _ _ _ B h hc w0 hw m ξ hξ G hG
  obtain ⟨u, φ, rfl⟩ := hξ
  have hI : ∀ Y : AA k d, Y ∈ Ig R k (Fin d ⊕ Fin d) → IntAA (R := R) k Y := by
    rintro Y ⟨g, rfl⟩ n
    exact ⟨MvPowerSeries.coeff n g, by rw [MvPowerSeries.coeff_map]⟩
  exact hI _ (exp_conj_connection_integral hc w0 hw m u φ G (ig_of_intAA hG))

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
