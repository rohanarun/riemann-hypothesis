module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0550
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0563
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0528
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IpSmulRight
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em
open IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.OrbExist

variable {D : D7} {a b c n r t : ℕ}

theorem adj_rat_herm (b₀ : HermE D r) : adj (rat b₀.1) = rat b₀.1 := by
  have hb := b₀.2
  ext i j
  have h2 : D.sp.cm.sig (b₀.1 j i) = b₀.1 i j := by
    have := congrFun (congrFun hb i) j
    simpa using this
  change cA D (incA D (b₀.1 j i)) = incA D (b₀.1 i j)
  rw [← h2]
  rfl

theorem rat_inv_mul (b₀ : HermE D r) (hb : b₀.1.det ≠ 0) : mm (rat b₀.1⁻¹) (rat b₀.1) = (1 : Mx D r r) := by
  have h : b₀.1⁻¹ * b₀.1 = 1 := Matrix.nonsing_inv_mul _ (Ne.isUnit hb)
  have := congrArg (fun M : Matrix (Fin r) (Fin r) D.host.E => M.map (incA D)) h
  simpa [rat, mm, Matrix.map_mul] using this

theorem rat_mul_inv (b₀ : HermE D r) (hb : b₀.1.det ≠ 0) : mm (rat b₀.1) (rat b₀.1⁻¹) = (1 : Mx D r r) := by
  have h : b₀.1 * b₀.1⁻¹ = 1 := Matrix.mul_nonsing_inv _ (Ne.isUnit hb)
  have := congrArg (fun M : Matrix (Fin r) (Fin r) D.host.E => M.map (incA D)) h
  simpa [rat, mm, Matrix.map_mul] using this

theorem adj_ip (V : HSp D) (x : Mx D V.rank a) (y : Mx D V.rank b) : adj (ip V x y) = ip V y x := by
  unfold ip mm
  rw [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]

theorem adj_add_r (x y : Mx D a b) : adj (x + y) = adj x + adj y := by
  ext i j
  simp [adj]

theorem adj_one_r : adj (1 : Mx D a a) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [adj]
  · have h' : j ≠ i := fun q => h q.symm
    simp [adj, Matrix.one_apply, h, h']

theorem adj_rat_inv (b₀ : HermE D r) (hb : b₀.1.det ≠ 0) : adj (rat b₀.1⁻¹) = rat b₀.1⁻¹ := by
  have h1 : adj (mm (rat b₀.1⁻¹) (rat b₀.1)) = 1 := by rw [rat_inv_mul b₀ hb, adj_one_r]
  have h2 : mm (rat b₀.1) (adj (rat b₀.1⁻¹)) = 1 := by
    have := h1
    simp only [mm] at this ⊢
    rwa [adj_mul, adj_rat_herm] at this
  have h3 := congrArg (fun M : Mx D r r => mm (rat b₀.1⁻¹) M) h2
  simp only [mm] at h3
  have h4 : mm (rat b₀.1⁻¹) (rat b₀.1) = (1 : Mx D r r) := rat_inv_mul b₀ hb
  simp only [mm] at h4
  rwa [← Matrix.mul_assoc, h4, Matrix.one_mul, Matrix.mul_one] at h3

theorem ip_add_right (V : HSp D) (x : Mx D V.rank a) (y y' : Mx D V.rank b) :
    ip V x (y + y') = ip V x y + ip V x y' := by
  unfold ip mm
  rw [Matrix.mul_add, Matrix.mul_add]

theorem ip_add_left (V : HSp D) (x x' : Mx D V.rank a) (y : Mx D V.rank b) :
    ip V (x + x') y = ip V x y + ip V x' y := by
  unfold ip mm
  rw [adj_add_r, Matrix.add_mul]

theorem ip_mul_right (V : HSp D) (x : Mx D V.rank a) (y : Mx D V.rank b) (w : Mx D b c) :
    ip V x (mm y w) = mm (ip V x y) w := by
  unfold ip mm
  simp only [Matrix.mul_assoc]

theorem ip_mul_left (V : HSp D) (x : Mx D V.rank a) (y : Mx D V.rank b) (w : Mx D a c) :
    ip V (mm x w) y = mm (adj w) (ip V x y) := by
  unfold ip mm
  rw [adj_mul, Matrix.mul_assoc]

theorem ip_smul_right (V : HSp D) (e : AE D) (x : Mx D V.rank a) (y : Mx D V.rank b) :
    ip V x (e • y) = e • ip V x y := by
  unfold ip mm
  rw [Matrix.mul_smul, Matrix.mul_smul]

theorem qv_mem (V : HSp D) (b₀ : HermE D r) (z : Mx D V.rank r × Mx D V.rank t) : qv V b₀ z ∈ hermA D t := by
  change adj (qv V b₀ z) = qv V b₀ z
  have hp : adj (pr b₀ (yv V b₀ z) (yv V b₀ z)) = pr b₀ (yv V b₀ z) (yv V b₀ z) := by
    have hr : (b₀.1.map (incA D)) = rat b₀.1 := rfl
    unfold pr
    rw [hr, adj_mul, adj_mul, adj_adj, adj_rat_herm, Matrix.mul_assoc]
  have hs : ∀ x y : Mx D t t, adj (x - y) = adj x - adj y := by
    intro x y
    ext i j
    simp [adj]
  unfold qv
  rw [hs, hp, adj_ip]

theorem yv_smul (V : HSp D) (b₀ : HermE D r) (e : AE D) (z : Mx D V.rank r × Mx D V.rank t) (h : e • z.2 = z.2) :
    e • yv V b₀ z = yv V b₀ z := by
  unfold yv
  conv_rhs => rw [← h, ip_smul_right]
  simp only [mm]
  rw [Matrix.mul_smul]

theorem qv_smul (V : HSp D) (b₀ : HermE D r) (e : AE D) (z : Mx D V.rank r × Mx D V.rank t) (h : e • z.2 = z.2) :
    e • qv V b₀ z = qv V b₀ z := by
  have h1 : e • ip V z.2 z.2 = ip V z.2 z.2 := by
    have := ip_smul_right V e z.2 z.2
    rw [h] at this
    exact this.symm
  have h2 : e • pr b₀ (yv V b₀ z) (yv V b₀ z) = pr b₀ (yv V b₀ z) (yv V b₀ z) := by
    unfold pr
    rw [← Matrix.mul_smul, ← Matrix.mul_smul, yv_smul V b₀ e z h]
  unfold qv
  rw [smul_sub, h1, h2]

theorem pr_add (b₀ : HermE D r) (u u' w w' : Mx D r t) :
    pr b₀ (u + u') (w + w') = pr b₀ u w + pr b₀ u w' + (pr b₀ u' w + pr b₀ u' w') := by
  unfold pr
  rw [adj_add_r, Matrix.mul_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]

theorem alg4 {M : Type} [AddCommGroup M] (c p a a' s : M) :
    c + a + (a' + s) - (p + a + (a' + s)) = c - p := by abel

theorem qv_shear (V : HSp D) (b₀ : HermE D r) (hb : b₀.1.det ≠ 0) (e : AE D) (z₁ : Mx D V.rank r) (z₂ : Mx D V.rank t)
    (y : Mx D r t) (hG : ip V z₁ z₁ = e • rat b₀.1) (hy : e • y = y) :
    qv V b₀ (z₁, z₂ + mm z₁ y) = qv V b₀ (z₁, z₂) := by
  have hr : (b₀.1.map (incA D)) = rat b₀.1 := rfl
  have hGy : mm (ip V z₁ z₁) y = mm (rat b₀.1) y := by
    rw [hG]
    simp only [mm]
    rw [Matrix.smul_mul, ← Matrix.mul_smul, hy]
  have hyv : yv V b₀ (z₁, z₂ + mm z₁ y) = yv V b₀ (z₁, z₂) + y := by
    unfold yv
    simp only
    rw [ip_add_right, ip_mul_right, hGy]
    simp only [mm]
    rw [Matrix.mul_add, ← Matrix.mul_assoc]
    have := rat_inv_mul b₀ hb
    simp only [mm] at this
    rw [this, Matrix.one_mul]
  have hPi := rat_inv_mul b₀ hb
  have hPi' := rat_mul_inv b₀ hb
  have hu : adj (yv V b₀ (z₁, z₂)) = mm (ip V z₂ z₁) (rat b₀.1⁻¹) := by
    unfold yv
    simp only [mm]
    rw [adj_mul, adj_rat_inv b₀ hb, adj_ip]
  have hpu : ∀ w : Mx D r t, pr b₀ (yv V b₀ (z₁, z₂)) w = mm (ip V z₂ z₁) w := by
    intro w
    unfold pr
    rw [hu, hr]
    simp only [mm] at hPi ⊢
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (rat b₀.1⁻¹), hPi, Matrix.one_mul]
  have hpu' : ∀ w : Mx D r t, pr b₀ w (yv V b₀ (z₁, z₂)) = mm (adj w) (ip V z₁ z₂) := by
    intro w
    unfold pr yv
    rw [hr]
    simp only [mm] at hPi' ⊢
    rw [← Matrix.mul_assoc (rat b₀.1), hPi', Matrix.one_mul]
  have hpyy : pr b₀ y y = mm (adj y) (mm (ip V z₁ z₁) y) := by
    rw [hGy, pr, hr]
  unfold qv
  rw [hyv]
  simp only
  rw [pr_add, hpu (yv V b₀ (z₁, z₂)), hpu y, hpu', hpyy, ip_add_left, ip_add_right, ip_add_right, ip_mul_left, ip_mul_left,
    ip_mul_right, ip_mul_right]
  exact alg4 _ _ _ _ _

theorem qv_col (V : HSp D) (b₀ : HermE D r) (z₁ : Mx D V.rank r) (z₂ : Mx D V.rank t) (g : Mx D t t) :
    qv V b₀ (z₁, mm z₂ g) = mm (mm (adj g) (qv V b₀ (z₁, z₂))) g := by
  have hyv : yv V b₀ (z₁, mm z₂ g) = mm (yv V b₀ (z₁, z₂)) g := by
    unfold yv
    simp only
    rw [ip_mul_right]
    simp only [mm]
    rw [Matrix.mul_assoc]
  unfold qv
  rw [hyv]
  simp only
  rw [ip_mul_left, ip_mul_right]
  unfold pr
  simp only [mm]
  rw [adj_mul, Matrix.mul_sub, Matrix.sub_mul]
  simp only [Matrix.mul_assoc]

theorem pch_conj (ψ : AddChar (AF D.host.F) ℂ) (x q h : Mx D t t) :
    pch ψ x (mm (mm (adj h) q) h) = pch ψ (mm (mm h x) (adj h)) q := by
  unfold pch
  congr 2
  simp only [mm]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.OrbExist

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAnalyticUniformizationOfIsAnalyticIso
section
open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

noncomputable section

namespace GlobalTheory.CompanionTheory.EllipticCM

open _root_.WeierstrassCurve GroundTheory.Global.Elliptic GroundTheory.Arith.Abelian

theorem variableChangePoint_latticePoint {X : WeierstrassCurve ℂ} {L : PeriodPair}
    {C : VariableChange ℂ} (h : C • X = GlobalTheory.latticeCurve L) (h' : C⁻¹ • weierstrassCurve L = X)
    (z : ℂ) :
    GlobalTheory.variableChangePoint C h (GlobalTheory.latticePoint L z) = vcPoint C⁻¹ h' (toPoint L z) := by
  by_cases hz : z ∈ L.lattice
  · rw [GlobalTheory.latticePoint_of_mem L hz, toPoint_of_mem hz, map_zero, vcPoint_zero]
  · rw [GlobalTheory.latticePoint_of_notMem L hz, toPoint_of_notMem hz, GlobalTheory.variableChangePoint_some,
      vcPoint_some, Affine.Point.some.injEq]
    have hu : (C.u : ℂ) ≠ 0 := C.u.ne_zero
    constructor
    · simp only [vcX, VariableChange.inv_def, inv_inv, Units.val_inv_eq_inv_val]
      field_simp
      ring
    · simp only [vcY, VariableChange.inv_def, inv_inv, Units.val_inv_eq_inv_val]
      field_simp
      ring

theorem isAnalyticUniformization_of_isAnalyticIso {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] [Algebra K ℂ] (_h2 : Module.finrank ℚ K = 2) (X : WeierstrassCurve ℂ)
    [X.IsElliptic] (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (_h𝔞 : 𝔞 ≠ 0)
    (ξ : (ℂ ⧸ GlobalTheory.EllipticCM.idealSub 𝔞) ≃+ X.toAffine.Point)
    (hξ : GlobalTheory.EllipticCM.IsAnalyticIso ξ) :
    GroundTheory.Global.Elliptic.IsAnalyticUniformization
      (GroundTheory.Global.Elliptic.idealLattice (algebraMap K ℂ) 𝔞)
      (ξ.toAddMonoidHom.comp (QuotientAddGroup.mk' _)) := by
  obtain ⟨L, C, h⟩ := GlobalTheory.exists_variableChange_eq_latticeCurve X
  obtain ⟨α, hα, hΛ, hz⟩ := hξ.exists_mul h
  have e : GlobalTheory.latticeCurve L = weierstrassCurve L := by
    simp [GlobalTheory.latticeCurve, weierstrassCurve, neg_div]
  have h' : C⁻¹ • weierstrassCurve L = X := by
    rw [← e, ← h, inv_smul_smul]
  have hΛ' : ∀ z, z ∈ idealLattice (algebraMap K ℂ) 𝔞 ↔ α * z ∈ L.lattice := fun z => by
    rw [← hΛ]
    rfl
  open Complex Filter _root_.Topology Set in
  open scoped PeriodPair in
  have hf0 :
      IsAnalyticUniformization L.lattice (toPointHom L) := by
    refine {
      map_eq_zero_iff := fun z ↦ toPoint_eq_zero_iff
      surjective := toPoint_surjective
      analyticAt_affine := ?analyticAt_affine
      analyticAt_infinity := ?analyticAt_infinity }
    case analyticAt_affine =>
      intro z hz
      have hz' : z ∉ L.lattice := fun h ↦ hz (toPoint_of_mem h)
      refine ⟨℘[L], fun w ↦ ℘'[L] w / 2, L.analyticOnNhd_weierstrassP z hz',
        (L.analyticOnNhd_derivWeierstrassP z hz').div_const, ?_⟩
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz'] with w hw
      exact ⟨_, toPoint_of_notMem hw⟩
    case analyticAt_infinity =>
      intro z hz
      have hzL : z ∈ L.lattice := toPoint_eq_zero_iff.1 hz
      set F : ℂ → ℂ := fun w ↦ ℘[L] w / (℘'[L] w / 2)
      set G : ℂ → ℂ := fun w ↦ 1 / (℘'[L] w / 2)
      have hP := L.meromorphic_weierstrassP z
      have hD : MeromorphicAt (fun w ↦ ℘'[L] w / 2) z := (L.meromorphic_derivWeierstrassP z).div
        (MeromorphicAt.const 2 z)
      have oD : meromorphicOrderAt (fun w ↦ ℘'[L] w / 2) z = -3 := by
        have e : (fun w ↦ ℘'[L] w / 2) = (fun _ ↦ (2 : ℂ)⁻¹) * ℘'[L] := by
          funext w; simp only [Pi.mul_apply]; ring
        rw [e, meromorphicOrderAt_mul_of_ne_zero analyticAt_const (by norm_num),
          meromorphicOrderAt_derivWeierstrassP L hzL]
      have hF : MeromorphicAt F z := hP.div hD
      have hG : MeromorphicAt G z := (MeromorphicAt.const 1 z).div hD
      have oF : meromorphicOrderAt F z = 1 := by
        rw [show F = ℘[L] * (fun w ↦ ℘'[L] w / 2)⁻¹ from funext fun w ↦ div_eq_mul_inv _ _,
          meromorphicOrderAt_mul hP hD.inv, meromorphicOrderAt_inv, oD,
          L.order_weierstrassP z hzL]
        rfl
      have oG : meromorphicOrderAt G z = 3 := by
        rw [show G = (fun w ↦ ℘'[L] w / 2)⁻¹ from funext fun w ↦ one_div _,
          meromorphicOrderAt_inv, oD]
        rfl
      have hFz : limPunctured F z = 0 := limPunctured_eq_zero_of_pos (by rw [oF]; exact zero_lt_one)
      have hGz : limPunctured G z = 0 := limPunctured_eq_zero_of_pos (by rw [oG]; norm_num)
      refine ⟨limPunctured F, limPunctured G,
        analyticAt_limPunctured hF (by rw [oF]; exact zero_le_one),
        analyticAt_limPunctured hG (by rw [oG]; norm_num), ?_⟩
      have hne : ∀ᶠ w in 𝓝[≠] z, w ∉ L.lattice ∧ ℘'[L] w / 2 ≠ 0 := by
        refine (eventually_nhdsWithin_iff.2 ?_).and
          ((meromorphicOrderAt_ne_top_iff_eventually_ne_zero hD).1 (by rw [oD]; decide))
        filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds z] with w hw hwz hwL
        exact hw ⟨hwL, hwz⟩
      rw [eventually_nhdsWithin_iff] at hne
      filter_upwards [hne] with w hw
      by_cases hwz : w = z
      · subst hwz
        exact Or.inl ⟨hz, hFz, hGz⟩
      obtain ⟨hwL, hw0⟩ := hw hwz
      have hDa : AnalyticAt ℂ (fun w ↦ ℘'[L] w / 2) w :=
        (L.analyticOnNhd_derivWeierstrassP w hwL).div_const
      have hFw : limPunctured F w = F w := limPunctured_eq_of_continuousAt
        ((L.analyticOnNhd_weierstrassP w hwL).div hDa hw0).continuousAt
      have hGw : limPunctured G w = G w := limPunctured_eq_of_continuousAt
        (analyticAt_const.div hDa hw0).continuousAt
      have hGne : G w ≠ 0 := one_div_ne_zero hw0
      have hw0' : ℘'[L] w ≠ 0 := fun h ↦ hw0 (by rw [h, zero_div])
      have e1 : F w / G w = ℘[L] w := by
        simp only [F, G]; field_simp
      have e2 : 1 / G w = ℘'[L] w / 2 := by
        simp only [G]; field_simp
      refine Or.inr ⟨by rw [hGw]; exact hGne, ?_⟩
      rw [hFw, hGw]
      refine ⟨by rw [e1, e2]; exact WeierstrassCurve.Affine.equation_iff_nonsingular.1 (equation_weierstrassP L hwL), ?_⟩
      show toPoint L w = _
      rw [toPoint_of_notMem hwL]
      exact point_some_congr e1.symm e2.symm
  have hvc {Λ : Submodule ℤ ℂ} {E E' : WeierstrassCurve ℂ} {f : ℂ →+ E.toAffine.Point}
  (hf : IsAnalyticUniformization Λ f) (C : VariableChange ℂ)
      (h : C • E = E') : IsAnalyticUniformization Λ ((vcPointEquiv C h).toAddMonoidHom.comp f) := by
    refine {
      map_eq_zero_iff := ?map_eq_zero_iff
      surjective := (vcPointEquiv C h).surjective.comp hf.surjective
      analyticAt_affine := ?analyticAt_affine
      analyticAt_infinity := ?analyticAt_infinity }
    case map_eq_zero_iff =>
      intro z
      rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, vcPointEquiv_apply, vcPoint_eq_zero_iff,
        hf.map_eq_zero_iff]
    case analyticAt_affine =>
      intro z hz
      have hz' : f z ≠ 0 := fun h0 ↦ hz (by
        rw [AddMonoidHom.comp_apply, h0, map_zero])
      obtain ⟨X, Y, hX, hY, hev⟩ := hf.analyticAt_affine z hz'
      refine ⟨fun w ↦ vcX C (X w), fun w ↦ vcY C (X w) (Y w), ?_, ?_, ?_⟩
      · simp only [vcX]; fun_prop
      · simp only [vcY]; fun_prop
      filter_upwards [hev] with w ⟨hw, e⟩
      rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, vcPointEquiv_apply, e, vcPoint_some]
      exact ⟨_, rfl⟩
    case analyticAt_infinity =>
      intro z hz
      have hz' : f z = 0 := by
        rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, vcPointEquiv_apply,
          vcPoint_eq_zero_iff] at hz
        exact hz
      obtain ⟨U, V, hU, hV, hev⟩ := hf.analyticAt_infinity z hz'
      have h0 : U z = 0 ∧ V z = 0 := by
        rcases hev.self_of_nhds with ⟨-, hU0, hV0⟩ | ⟨-, h1, e⟩
        · exact ⟨hU0, hV0⟩
        · exact absurd (e.symm.trans hz') (Affine.Point.some_ne_zero _)
      set v : ℂ := ((C.u⁻¹ : ℂˣ) : ℂ)
      have hv : v ≠ 0 := Units.ne_zero _
      set D : ℂ → ℂ := fun w ↦ 1 - C.s * U w + C.s * C.r * V w - C.t * V w
      have hD : AnalyticAt ℂ D z := by simp only [D]; fun_prop
      have hDz : D z = 1 := by simp only [D, h0.1, h0.2]; ring
      have hDne : ∀ᶠ w in 𝓝 z, D w ≠ 0 :=
        hD.continuousAt.eventually_ne (by rw [hDz]; exact one_ne_zero)
      refine ⟨fun w ↦ (U w - C.r * V w) / (v * D w), fun w ↦ V w / (v ^ 3 * D w), ?_, ?_, ?_⟩
      · exact (hU.sub (analyticAt_const.mul hV)).div (analyticAt_const.mul hD)
          (mul_ne_zero hv (by rw [hDz]; exact one_ne_zero))
      · exact hV.div (analyticAt_const.mul hD) (mul_ne_zero (pow_ne_zero 3 hv) (by rw [hDz]; exact one_ne_zero))
      filter_upwards [hev, hDne] with w hw hDw
      rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, vcPointEquiv_apply]
      rcases hw with ⟨hf0, hU0, hV0⟩ | ⟨hV0, hw, e⟩
      · left
        rw [hf0]
        exact ⟨rfl, by rw [hU0, hV0]; simp, by rw [hV0]; simp⟩
      · right
        refine ⟨div_ne_zero hV0 (mul_ne_zero (pow_ne_zero 3 hv) hDw), ?_⟩
        rw [e, vcPoint_some]
        apply exists_point_some_eq
        · simp only [vcX]
          field_simp
          ring
        · simp only [vcY, D]
          field_simp
          ring
  have hmul
  {Λ Λ' : Submodule ℤ ℂ} {E : WeierstrassCurve ℂ}
      {f : ℂ →+ E.toAffine.Point} (hf : IsAnalyticUniformization Λ f) {c : ℂ} (hc : c ≠ 0)
      (hΛ : ∀ z, z ∈ Λ' ↔ c * z ∈ Λ) :
      IsAnalyticUniformization Λ' (f.comp (AddMonoidHom.mulLeft c)) := by
    refine {
      map_eq_zero_iff := ?map_eq_zero_iff
      surjective := ?surjective
      analyticAt_affine := ?analyticAt_affine
      analyticAt_infinity := ?analyticAt_infinity }
    case map_eq_zero_iff =>
      intro z
      rw [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, hf.map_eq_zero_iff, hΛ]
    case surjective =>
      intro P
      obtain ⟨y, rfl⟩ := hf.surjective P
      exact ⟨c⁻¹ * y, by rw [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, mul_inv_cancel_left₀ hc]⟩
    case analyticAt_affine =>
      intro z hz
      obtain ⟨X, Y, hX, hY, hev⟩ := hf.analyticAt_affine (c * z) hz
      have ht : Tendsto (fun w ↦ c * w) (𝓝 z) (𝓝 (c * z)) := (continuous_const_mul c).tendsto z
      refine ⟨fun w ↦ X (c * w), fun w ↦ Y (c * w), hX.comp_of_eq (by fun_prop) rfl,
        hY.comp_of_eq (by fun_prop) rfl, ?_⟩
      filter_upwards [ht.eventually hev] with w hw
      exact hw
    case analyticAt_infinity =>
      intro z hz
      obtain ⟨U, V, hU, hV, hev⟩ := hf.analyticAt_infinity (c * z) hz
      have ht : Tendsto (fun w ↦ c * w) (𝓝 z) (𝓝 (c * z)) := (continuous_const_mul c).tendsto z
      refine ⟨fun w ↦ U (c * w), fun w ↦ V (c * w), hU.comp_of_eq (by fun_prop) rfl,
        hV.comp_of_eq (by fun_prop) rfl, ?_⟩
      filter_upwards [ht.eventually hev] with w hw
      exact hw
  have hf := hvc (hmul hf0 hα hΛ') C⁻¹ h'
  convert hf using 1
  ext z
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, vcPointEquiv_apply,
    AddMonoidHom.coe_mulLeft]
  exact (hz z).trans (variableChangePoint_latticePoint h h' _)

end GlobalTheory.CompanionTheory.EllipticCM
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogNormContinuousOffDivisorStatement
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_norm_continuous_off_divisor : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ : k →+* ℂ}
    {L : LB X} (ψ : GlobalTheory.Weight q σ L), ψ.IsCInf → ∀ {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r),
    ContinuousOn (GlobalTheory.Cartier.logNorm ψ r) (offSupp q σ (divOfRatSec ψ.isLB hr)) := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchInt.continuousOn_logNorm_offSupp | exact GlobalTheory.CompanionTheory.MixZ.ArchInt.continuousOn_logNorm_offSupp | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchInt.continuousOn_logNorm_offSupp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPointEqPointMapRing
section
open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.ConjPointDict

theorem mapPoint_eq_pointMapRing : ∀ [DecidableEq ℂ] (X : WeierstrassCurve ℂ) (σ : ℂ →+* ℂ)
    (P : X.toAffine.Point), GlobalTheory.ConjPoint.mapPoint X σ P = GroundTheory.Global.pointMapRing σ X P := by
  intro _ X σ P
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · obtain ⟨h', e⟩ := GroundTheory.Global.pointMapRing_some σ X h
    rw [e]
    rfl

end GlobalTheory.CompanionTheory.ConjPointDict
end

