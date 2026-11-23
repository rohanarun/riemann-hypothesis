module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0029
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0005

@[expose] public section
set_option synthInstance.maxHeartbeats 200000

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceIrr
section
open IsLocalRing Matrix Polynomial UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.W UpperTheory.V.Pr

private theorem chi_map_ofRep {n : ℕ} {A K G : Type} [CommRing A] [CommRing K] [Group G] (f : A →+* K)
    (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    ((GDet.ofRep ρ).map f).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly.map f := by
  letI : Algebra A K[X] := ((algebraMap K K[X]).comp f).toAlgebra
  rw [← Matrix.charpoly_map]
  change (GDet.repAlg ρ K[X] _).det = (Matrix.charmatrix _).det
  congr 1
  ext i j : 1
  have h : ∀ a, algebraMap A K[X] a = C (f a) := fun _ => rfl
  by_cases hij : i = j
  · subst hij
    simp [GDet.repAlg, h]
  · simp [GDet.repAlg, h, hij]

private theorem charpoly_flag {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k)
    (κ : Fin n → H →* kˣ) (h : HasFlag r κ) (s : H) : (gm r s).charpoly = chPoly κ s := by
  obtain ⟨g, hg⟩ := h
  have h1 := Matrix.charpoly_units_conj g (gm r s)
  have h2 : ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular id :=
    fun i j hij => (hg s).1 i j hij
  have h3 := Matrix.charpoly_of_upperTriangular _ h2
  rw [← h1]
  simp only [Units.val_mul, Matrix.coe_units_inv] at h3
  rw [h3]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h4 := (hg s).2 i
  simp only [Units.val_mul, Matrix.coe_units_inv] at h4
  rw [h4]

private theorem irr_twist {G H k : Type} [Group G] [Group H] [Field k] {n : ℕ} (a : G → Matrix (Fin n) (Fin n) k)
    (b : H → Matrix (Fin n) (Fin n) k) (π : G → H) (hπ : Function.Surjective π) (c : G → kˣ)
    (h : ∀ g, a g = (c g : k) • b (π g)) (hb : MatIrr ⊤ b) : MatIrr ⊤ a := by
  intro W hW
  refine hb W fun s _ v hv => ?_
  obtain ⟨g, rfl⟩ := hπ s
  have h1 := W.smul_mem ((c g)⁻¹ : kˣ) (hW g trivial v hv)
  rwa [h, Matrix.smul_mulVec, smul_smul, Units.inv_mul, one_smul] at h1

private theorem w_ne {k : Type} [Field k] {n : ℕ} (hn : n = 2 ∨ n = 3) (a : kˣ) (ha : a ^ 2 ≠ 1) :
    ∃ i j : Fin n, a ^ w n i ≠ a ^ w n j := by
  rcases hn with rfl | rfl
  · refine ⟨0, 1, fun h => ha ?_⟩
    have h1 : a ^ (1 : ℤ) = a ^ (-1 : ℤ) := h
    rw [zpow_one, _root_.zpow_neg_one] at h1
    rw [sq]
    exact mul_eq_one_iff_eq_inv.2 h1
  · refine ⟨0, 2, fun h => ha ?_⟩
    have h1 : a ^ (1 : ℤ) = a ^ (-1 : ℤ) := h
    rw [zpow_one, _root_.zpow_neg_one] at h1
    rw [sq]
    exact mul_eq_one_iff_eq_inv.2 h1

theorem UpperTheory.V.Pr.niceIrr :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (n : ℕ) (T : UpperTheory.V.Pr.Setup F n) (x : Ideal T.S.A) (L : T.S.Loc x) (y : UpperTheory.V.W.Point T.r) (j : L.R →ₐ[O] y.A), IsLocalHom j → UpperTheory.V.Pr.Nice L.ρ (RingHom.ker j) → UpperTheory.V.W.mat y.ρ = T.K.tw (L.ρ.map (j : L.R →+* y.A)) → y.ψ = T.K.twψ (L.ρ.map (j : L.R →+* y.A)) → L.ρ.TI (RingHom.ker j) → ∀ U : Subgroup T.G.G₀, IsOpen (U : Set T.G.G₀) → UpperTheory.V.U3.MatIrr (U ⊓ T.G.G') (UpperTheory.V.W.mat (UpperTheory.V.W.pushRep (algebraMap y.Fr y.Fb) y.ρF)) := by
  intro l _ O _ _ _ _ _ F n T x L y j hj hp h1 h2 hI U hU
  classical
  let φ : y.A →+* y.Fb := (algebraMap y.Fr y.Fb).comp (algebraMap y.A y.Fr)
  have hφ : Function.Injective φ := (algebraMap y.Fr y.Fb).injective.comp (IsFractionRing.injective y.A y.Fr)
  have hm : ∀ g, gm (pushRep (algebraMap y.Fr y.Fb) y.ρF) g = (mat y.ρ g).map φ := fun g => rfl
  have hn : n.Prime := by
    rcases T.n23 with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three

  have hirr : MatIrr ⊤ (gm (pushRep (algebraMap y.Fr y.Fb) y.ρF)) := by
    let f : T.S.A →+* y.Fb := φ.comp ((j : L.R →+* y.A).comp (L.ι : T.S.A →+* L.R))
    have hker : RingHom.ker f = L.im (RingHom.ker j) := by
      ext a
      exact (map_eq_zero_iff φ hφ).trans Iff.rfl
    obtain ⟨k1, k2, k3⟩ := (loc_rho T.ok T.n23 T.S x L).2.2.1 (RingHom.ker j)
    have hTI : T.S.u.TI (RingHom.ker f) := by
      rw [hker]
      exact ⟨⟨fun h => hI.1.1 (k1.2 h), fun h => hI.1.2 (k2.2 h)⟩, fun h3 h => hI.2 h3 (k3.2 h)⟩
    refine irr_twist _ _ T.K.π T.K.π_surj (fun g => Units.map φ.toMonoidHom (T.K.κA y.A g)) (fun g => ?_)
      ((types T.ok T.n23 T.S y.Fb f).1.2 hTI)
    rw [hm, h1]
    ext a b
    exact map_mul φ _ _

  have hred : RedTo (pushRep (algebraMap y.Fr y.Fb) y.ρF) φ (PowerSeries.constantCoeff : y.A →+* y.K)
      fun i => pushCh (algebraMap (ResidueField O) y.K) (T.r.chib i) := by
    intro g
    refine ⟨(mat y.ρ g).charpoly, by rw [hm, Matrix.charpoly_map], ?_⟩
    have h := congrArg (fun D => GDet.chi D (MonoidAlgebra.single g 1)) y.red
    simp only [Resid.Dbar, chi_map_ofRep] at h
    rw [h]
    change (Matrix.diagonal _).charpoly.map _ = _
    rw [Matrix.charpoly_diagonal, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl

  have hV : Nonempty F.V := by
    by_contra hV
    rw [not_nonempty_iff] at hV
    have h := T.big.1
    simp [Frame.d] at h
  obtain ⟨v'⟩ := hV
  obtain ⟨v, rfl⟩ := T.K.e.surjective v'

  have hfi : U.FiniteIndex := by
    haveI : CompactSpace T.G.G₀ :=
      isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ T.G.η_open).isCompact
    haveI := Subgroup.quotient_finite_of_isOpen U hU
    exact Subgroup.finiteIndex_of_finite_quotient
  have hUo : IsOpen (U.normalCore : Set T.G.G₀) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (Subgroup.normalCore_isClosed U (Subgroup.isClosed_of_isOpen U hU))
  haveI : T.G.G'.Normal := MonoidHom.normal_ker _
  have key := irrNormal T.G.G₀ y.Fb y.K y.A n hn (pushRep (algebraMap y.Fr y.Fb) y.ρF) hirr φ _ _ hφ hred
    (T.G.Gv v) (T.G.φ v) (fun i => pushCh φ (y.ψ v i)) (fun g => ?_) (U.normalCore ⊓ T.G.G') (fun a b hab => ?_) ?_
  · intro W hW
    exact key W fun g hg => hW g ⟨U.normalCore_le hg.1, hg.2⟩
  · have h := congrArg (Polynomial.map (algebraMap y.Fr y.Fb)) (charpoly_flag _ _ (y.flag v) g)
    rw [← Matrix.charpoly_map, chPoly, Polynomial.map_prod] at h
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at h
    exact h
  · obtain ⟨g, hg, hfr⟩ := niceSep l O F n T x L y j hj hp h1 h2 U.normalCore hUo v
    refine ⟨g, hg, fun h => hfr a b hab 1 one_pos ?_⟩
    rw [pow_one, pow_one]
    exact Units.ext ((algebraMap y.Fr y.Fb).injective (congrArg Units.val h))
  · obtain ⟨s, hs⟩ := T.ok.f3 (T.K.e v)
    obtain ⟨g, rfl⟩ := (T.K.lam v).surjective s
    obtain ⟨a, b, hab⟩ := w_ne T.n23 _ hs
    refine ⟨a, b, g, fun h => hab ?_⟩
    have h3 : T.r.chib a (T.G.φ v g) = T.r.chib b (T.G.φ v g) :=
      Units.ext ((algebraMap (ResidueField O) y.K).injective (congrArg Units.val h))
    rw [T.K.chib, T.K.chib, ← T.K.lam_loc] at h3
    exact mul_right_cancel h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceIrrE
section
open Matrix Polynomial IsLocalRing UpperTheory.V.U3 UpperTheory.V.Fr

namespace UpperTheory.V.Pr

private def IsBlockDiagFinThree {A : Type} [CommRing A] (M : Matrix (Fin 3) (Fin 3) A) : Prop :=
  M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 1 2 = 0 ∧ M 2 1 = 0

private lemma submatrix_corners_three {A : Type} (M : Matrix (Fin 3) (Fin 3) A) :
    M.submatrix ![0, 2] ![0, 2] = !![M 0 0, M 0 2; M 2 0, M 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private lemma charpoly_block_three {A : Type} [CommRing A] (M : Matrix (Fin 3) (Fin 3) A) (h : IsBlockDiagFinThree M) :
    M.charpoly = (X - C (M 1 1)) * (M.submatrix ![0, 2] ![0, 2]).charpoly := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [submatrix_corners_three, Matrix.charpoly, det_fin_three, det_fin_two]
  simp [charmatrix_apply, h1, h2, h3, h4]
  ring

private def corner {G A : Type} [Group G] [CommRing A] (m : G →* Matrix (Fin 3) (Fin 3) A) (h : ∀ g, IsBlockDiagFinThree (m g)) :
    G →* Matrix (Fin 2) (Fin 2) A where
  toFun g := (m g).submatrix ![0, 2] ![0, 2]
  map_one' := by
    rw [submatrix_corners_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' g g' := by
    obtain ⟨h1, h2, h3, h4⟩ := h g
    rw [submatrix_corners_three, submatrix_corners_three, submatrix_corners_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h1, h4]

private lemma mid_eq {D κ : Type} [Field κ] (m : D → Matrix (Fin 3) (Fin 3) κ) (h : ∀ g, IsBlockDiagFinThree (m g))
    (ψ : Fin 3 → D → κ) (ho : ∀ g, ordProd m ψ g = 0) : ∃ i, ∀ g, m g 1 1 = ψ i g := by
  by_contra hc
  push Not at hc
  choose g hg using hc
  have h0 := congrFun (congrFun (ho g) 1) 1
  obtain ⟨a1, a2, a3, a4⟩ := h (g 0)
  obtain ⟨b1, b2, b3, b4⟩ := h (g 2)
  simp [ordProd, List.ofFn_succ, Matrix.mul_apply, Fin.sum_univ_three, a2, a3, b1, b4, sub_eq_zero] at h0
  rcases h0 with h0 | h0 | h0
  · exact hg 0 h0
  · exact hg 1 h0
  · exact hg 2 h0

private lemma core {G D κ k A : Type} [Group G] [Group D] [Field κ] [IsAlgClosed κ] [Field k] [CommRing A]
    (m : G →* Matrix (Fin 3) (Fin 3) A) (h : ∀ g, IsBlockDiagFinThree (m g)) (φ : A →+* κ) (hφ : Function.Injective φ)
    (hirr : MatIrr (⊤ : Subgroup G) fun g => ((m g).map φ).submatrix ![0, 2] ![0, 2])
    (red : A →+* k) (χ : Fin 2 → G →* kˣ) (h0 : ∀ g, red (m g 0 0) = χ 0 g) (h2 : ∀ g, red (m g 2 2) = χ 1 g)
    (h02 : ∀ g, red (m g 0 2) * red (m g 2 0) = 0) (ι : D →* G) (ψ : Fin 3 → D →* κˣ)
    (hch : ∀ g, ((m (ι g)).map φ).charpoly = chPoly ψ g)
    (ho : ∀ g, ordProd (fun s => (m (ι s)).map φ) (fun i s => (ψ i s : κ)) g = 0)
    (U : Subgroup G) [U.Normal] (hs : ∃ g, ι g ∈ U ∧ ∀ a b, a ≠ b → ψ a g ≠ ψ b g)
    (hχ : ∃ g, χ 0 (ι g) ≠ χ 1 (ι g)) :
    MatIrr U fun g => ((m g).map φ).submatrix ![0, 2] ![0, 2] := by
  have hb : ∀ g, IsBlockDiagFinThree ((m g).map φ) := fun g => by
    obtain ⟨h1, h2, h3, h4⟩ := h g
    simp [IsBlockDiagFinThree, h1, h2, h3, h4]
  obtain ⟨i, hi⟩ := mid_eq _ (fun s => hb (ι s)) _ ho
  let σ : G →* GL (Fin 2) κ := (corner ((φ.mapMatrix : Matrix (Fin 3) (Fin 3) A →+* _).toMonoidHom.comp m) hb).toHomUnits
  have hσ : gm σ = fun g => ((m g).map φ).submatrix ![0, 2] ![0, 2] := rfl
  rw [← hσ] at hirr ⊢
  refine irrNormal G κ k A 2 Nat.prime_two σ hirr φ red χ hφ (fun g => ?_) D ι (fun a => ψ (i.succAbove a))
    (fun g => ?_) U (fun a b hab => ?_) ?_
  · refine ⟨((m g).submatrix ![0, 2] ![0, 2]).charpoly, ?_, ?_⟩
    · rw [← Matrix.charpoly_map]; rfl
    · rw [← Matrix.charpoly_map]
      simp only [submatrix_corners_three, Matrix.charpoly, det_fin_two, chPoly, Fin.prod_univ_two]
      simp [charmatrix_apply, h0, h2, mul_eq_zero.1 (h02 g)]
  · have e := hch g
    rw [charpoly_block_three _ (hb _), hi, chPoly, Fin.prod_univ_succAbove _ i] at e
    exact mul_left_cancel₀ (X_sub_C_ne_zero _) e
  · obtain ⟨g, hg, hg'⟩ := hs
    exact ⟨g, hg, hg' _ _ fun e => hab (Fin.succAbove_right_injective e)⟩
  · obtain ⟨g, hg⟩ := hχ
    exact ⟨0, 1, g, hg⟩

end UpperTheory.V.Pr

open Matrix Polynomial IsLocalRing UpperTheory.V UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Pr in
theorem UpperTheory.V.Pr.niceIrrE :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (T : UpperTheory.V.Pr.Setup F 3) (x : Ideal T.S.A) (L : T.S.Loc x) (y : UpperTheory.V.W.Point T.r) (j : L.R →ₐ[O] y.A), IsLocalHom j → UpperTheory.V.Pr.Nice L.ρ (RingHom.ker j) → UpperTheory.V.W.mat y.ρ = T.K.tw (L.ρ.map (j : L.R →+* y.A)) → y.ψ = T.K.twψ (L.ρ.map (j : L.R →+* y.A)) → L.ρ.TE (RingHom.ker j) → ∀ U : Subgroup T.G.G₀, IsOpen (U : Set T.G.G₀) → UpperTheory.V.U3.MatIrr (U ⊓ T.G.G') fun g => (UpperTheory.V.W.mat (UpperTheory.V.W.pushRep (algebraMap y.Fr y.Fb) y.ρF) g).submatrix ![0, 2] ![0, 2] := by
  intro l _ O _ _ _ _ _ F T x L y j hj hN hρ hψ hE U hU
  have hj' : IsLocalHom (j : L.R →+* y.A) := ⟨hj.map_nonunit⟩
  obtain ⟨-, hbar, hid, htri⟩ := loc_rho T.ok T.n23 T.S x L
  have hO : IsLocalHom (algebraMap O L.R) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 := ha.map j
    rw [AlgHom.commutes, PowerSeries.isUnit_iff_constantCoeff] at h1
    have h2 : residue O a = 0 := (residue_eq_zero_iff a).2 hna
    have h3 : PowerSeries.constantCoeff (algebraMap O y.A a) = algebraMap (ResidueField O) y.K (residue O a) := by
      rw [PowerSeries.algebraMap_apply, PowerSeries.constantCoeff_C, IsScalarTower.algebraMap_apply O (ResidueField O) y.K]
      rfl
    rw [h3, h2, map_zero] at h1
    exact not_isUnit_zero h1
  have hb := (hbar (ResidueField.map (algebraMap O L.R)) fun a => ResidueField.map_residue _ _).1
  set φ : y.A →+* y.Fb := (algebraMap y.Fr y.Fb).comp (algebraMap y.A y.Fr) with hφ
  have hφi : Function.Injective φ := (algebraMap y.Fr y.Fb).injective.comp (IsFractionRing.injective y.A y.Fr)
  set ρ := L.ρ.map (j : L.R →+* y.A) with hρd
  set f : T.S.A →+* y.Fb := φ.comp ((j : L.R →+* y.A).comp (L.ι : T.S.A →+* L.R)) with hf
  have hfρ : T.S.u.map f = ρ.map φ := rfl
  have hker : RingHom.ker f = L.im (RingHom.ker j) := by
    ext a
    simp only [hf, RingHom.mem_ker, Space.Loc.im, Ideal.mem_comap, RingHom.comp_apply, map_eq_zero_iff _ hφi]
    rfl
  have hTE : T.S.u.TE (RingHom.ker f) := by
    rw [hker]
    obtain ⟨a, b, c⟩ := hid (RingHom.ker j)
    exact ⟨⟨fun h => hE.1.1 (a.2 h), fun h => hE.1.2 (b.2 h)⟩, rfl, c.1 hE.2.2⟩
  have hirr := typeE T.ok T.S y.Fb f hTE
  have hodd : ∀ g a b, Odd (w 3 a - w 3 b) → ρ.r g a b = 0 := fun g a b h =>
    hE.2.2 (Ideal.subset_span ⟨g, a, b, h, rfl⟩)
  have hV : Nonempty T.G.Vl := by
    rw [T.K.e.nonempty_congr]
    by_contra hc
    rw [not_nonempty_iff] at hc
    have := T.big.1
    simp [Frame.d] at this
  obtain ⟨v⟩ := hV
  have hfi : U.FiniteIndex := by
    haveI : CompactSpace T.G.G₀ :=
      isCompact_iff_compactSpace.1 (T.G.η.ker.isClosed_of_isOpen T.G.η_open).isCompact
    haveI := U.quotient_finite_of_isOpen hU
    exact Subgroup.finiteIndex_of_finite_quotient
  have hU' : IsOpen (U.normalCore : Set T.G.G₀) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (U.normalCore_isClosed (U.isClosed_of_isOpen hU))
  obtain ⟨g₁, hg₁, hfree⟩ := niceSep l O F 3 T x L y j hj hN hρ hψ _ hU' v
  haveI : T.G.G'.Normal := MonoidHom.normal_ker _
  let lam : T.G.Gv v →* F.Gv (T.K.e v) := (T.K.lam v).toMulEquiv.toMonoidHom
  have hlam : ∀ s, T.K.π (T.G.φ v s) = F.loc0 _ (lam s) := fun s => (T.K.lam_loc v s).symm
  let k' : ResidueField O →+* ResidueField y.A :=
    (ResidueField.map (j : L.R →+* y.A)).comp (ResidueField.map (algebraMap O L.R))
  have hres : ∀ z : L.R, residue y.A (j z) = ResidueField.map (j : L.R →+* y.A) (residue L.R z) := fun z =>
    (ResidueField.map_residue (j : L.R →+* y.A) z).symm
  have key := core (ρ.r.comp T.K.π)
    (fun g => ⟨hodd _ _ _ (by decide), hodd _ _ _ (by decide), hodd _ _ _ (by decide), hodd _ _ _ (by decide)⟩) φ hφi
    (fun W hW => hirr W fun g _ u hu => by
      obtain ⟨g', rfl⟩ := T.K.π_surj g
      exact hW g' trivial u hu)
    (residue y.A) (fun a => W.pushCh k' (((F.Ψ.comp F.del.ker.subtype).comp T.K.π) ^ w 3 (![0, 2] a)))
    (fun g => (hres _).trans (congrArg _ (hb (T.K.π g) 0))) (fun g => (hres _).trans (congrArg _ (hb (T.K.π g) 2)))
    (fun g => by
      rcases Classical.em (T.S.u.triP ≤ x) with hx | hx
      · have h1 : L.ρ.r (T.K.π g) 2 0 ∈ maximalIdeal L.R := by
          have := hx (Ideal.subset_span ⟨T.K.π g, 2, 0, by decide, rfl⟩)
          rw [← L.lies] at this
          exact this
        refine mul_eq_zero_of_right _ ((hres _).trans ?_)
        rw [(residue_eq_zero_iff _).2 h1, map_zero]
      · have h1 : L.ρ.r (T.K.π g) 0 2 ∈ maximalIdeal L.R :=
          (htri hx).2 (Ideal.subset_span ⟨T.K.π g, 0, 2, by decide, rfl⟩)
        refine mul_eq_zero_of_left ((hres _).trans ?_) _
        rw [(residue_eq_zero_iff _).2 h1, map_zero])
    (T.G.φ v) (fun i => ((ρ.map φ).ψ (T.K.e v) i).comp lam)
    (fun g => by
      have h := congrArg (Polynomial.map f) (o1 T.ok T.n23 T.S (T.K.e v) (lam g))
      rw [← Matrix.charpoly_map, Polynomial.map_prod] at h
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at h
      rw [MonoidHom.comp_apply, hlam]
      exact h)
    (fun g => by
      have h := (ρ.map φ).ord (T.K.e v) fun i => lam (g i)
      simp only [MonoidHom.comp_apply, hlam]
      exact h)
    (U.normalCore ⊓ T.G.G') ⟨g₁, hg₁, fun a b hab e => hfree a b hab 1 one_pos (by
      have e1 : φ (ρ.ψ (T.K.e v) a (lam g₁)) = φ (ρ.ψ (T.K.e v) b (lam g₁)) := congrArg Units.val e
      have e2 : ρ.ψ (T.K.e v) a (lam g₁) = ρ.ψ (T.K.e v) b (lam g₁) := Units.ext (hφi e1)
      have e3 : y.ψ v a g₁ = y.ψ v b g₁ := by
        rw [hψ]
        exact congrArg (· * _) e2
      simp only [e3])⟩
    (by
      obtain ⟨g, hg⟩ := T.ok.f3 (T.K.e v)
      obtain ⟨s, rfl⟩ := (T.K.lam v).surjective g
      refine ⟨s, fun e => hg ?_⟩
      have e1 : k' ((F.Ψ (T.K.π (T.G.φ v s)) ^ w 3 0 : (ResidueField O)ˣ) : ResidueField O) =
          k' ((F.Ψ (T.K.π (T.G.φ v s)) ^ w 3 2 : (ResidueField O)ˣ) : ResidueField O) := congrArg Units.val e
      have e2 := Units.ext (k'.injective e1)
      rw [hlam, show w 3 0 = 1 by decide, show w 3 2 = -1 by decide, zpow_one, _root_.zpow_neg_one] at e2
      rw [sq]
      exact mul_eq_one_iff_eq_inv.2 e2)
  intro Y hW
  refine key Y fun g hg u hu => ?_
  have h1 := hW g ⟨U.normalCore_le hg.1, hg.2⟩ u hu
  have h2 : (W.mat (W.pushRep (algebraMap y.Fr y.Fb) y.ρF) g).submatrix ![0, 2] ![0, 2] =
      φ (T.K.κA y.A g) • (((ρ.r.comp T.K.π) g).map φ).submatrix ![0, 2] ![0, 2] := by
    ext a b
    show φ (UpperTheory.V.W.mat y.ρ g _ _) = _
    rw [hρ]
    exact map_mul φ _ _
  simp only [h2, smul_mulVec] at h1
  exact (Y.smul_mem_iff (((T.K.κA y.A g).isUnit.map φ).ne_zero)).1 h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceSpecializationTwistSatisfiesFirstCondition
section
theorem UpperTheory.V.Pr.nice_specialization_twist_satisfies_first_condition :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (n : ℕ) (T : UpperTheory.V.Pr.Setup F n) (x : Ideal T.S.A) (L : T.S.Loc x) (y : UpperTheory.V.W.Point T.r) (j : L.R →ₐ[O] y.A), IsLocalHom j → UpperTheory.V.Pr.Nice L.ρ (RingHom.ker j) → UpperTheory.V.W.mat y.ρ = T.K.tw (L.ρ.map (j : L.R →+* y.A)) → y.ψ = T.K.twψ (L.ρ.map (j : L.R →+* y.A)) → y.N1 := by
  intro l _ O _ _ _ _ _ F n T x L y j hj hN hm hψ v
  obtain ⟨g, hgU, hfr⟩ := UpperTheory.V.Pr.niceSep l O F n T x L y j hj hN hm hψ ⊤
    (by simp) v
  have hG : T.G.φ v g ∈ T.G.G' := (Subgroup.mem_inf.mp hgU).2
  have he : (T.G.eps O y.A) (T.G.φ v g) = 1 := by
    rw [UpperTheory.V.W.GFrame.G', MonoidHom.mem_ker] at hG
    have hG' : T.G.ε ↑(T.G.φ v g) = 1 := hG
    simp [UpperTheory.V.W.GFrame.eps, UpperTheory.V.W.pushCh, hG']
  refine ⟨fun i k hik h => hfr i k hik 1 one_pos (by simp [h]), fun i k hik h => ?_⟩
  apply hfr i k (ne_of_lt hik) 1 one_pos
  simp [h, MonoidHom.mul_apply, he]
end

