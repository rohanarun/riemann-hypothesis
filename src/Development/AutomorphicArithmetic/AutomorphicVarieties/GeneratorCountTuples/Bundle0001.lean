module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LeftMultiplication.Lmul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.ConeHomotopyBoundaryFormula
section
open UpperTheory.V.ZK.PM
open UpperTheory.V.ZK hiding cone

private theorem hp_eq (A : Type) [CommRing A] (G : Type) [Group G] (k : G) :
    ∀ (m : ℕ) (z : Ch A G m), hp A k m z = hprism A (· * k) m z
  | 0, z => by rw [hprism_zero]; rfl
  | m + 1, z => ch_ext A (fun x => by
      have h := hprism_cone A (· * k) (x 0) m (Finsupp.single (Fin.tail (α := fun _ => G) x) 1)
      rw [← hmap_cone A (· * k), cone_single, Fin.cons_self_tail] at h
      rw [h, hp, Finsupp.linearCombination_single, one_smul, hp_eq A G k m, map_sub]
      rfl) z

theorem UpperTheory.coneHomotopy_boundary_formula :
    ∀ (A : Type) [CommRing A] (G : Type) [Group G] (k : G) (m : ℕ) (z : Ch A G (m + 1)), pr A G (m + 1) (hp A k (m + 1) z) = prism A k m (pr A G m z) := by
  intro A _ G _ k m z
  rw [hp_eq]
  exact (prism_toInh A k m z).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LeftMulChainChainHomotopic
section
open UpperTheory.V.ZK.PM
open UpperTheory.V.ZK hiding cone

section
variable (A : Type) [CommRing A] {G : Type} [Group G]

private theorem lmul_single (h : G) (m : ℕ) (x : Fin m → G) (a : A) :
    lmul A h m (Finsupp.single x a) = Finsupp.single (fun i => h * x i) a := by
  simp [lmul]

private theorem lmul_cone (h a : G) (m : ℕ) (y : Ch A G m) :
    lmul A h (m + 1) (PM.cone A a m y) = PM.cone A (h * a) m (lmul A h m y) := by
  simp only [lmul, PM.cone, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
  congr 1
  funext x i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

private theorem lmul_rmul (h k : G) (m : ℕ) (y : Ch A G m) :
    lmul A h m (rmul A k m y) = rmul A k m (lmul A h m y) := by
  simp only [lmul, rmul, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
  congr 1
  funext x i
  simp [mul_assoc]

private theorem pr_lmul (h : G) (m : ℕ) (y : Ch A G (m + 1)) :
    pr A G m (lmul A h (m + 1) y) = pr A G m y := by
  simp only [lmul, pr, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
  congr 1
  funext x i
  simp [mul_assoc]

private theorem lmul_hp (h k : G) : ∀ (m : ℕ) (y : Ch A G m),
    lmul A h (m + 1) (hp A k m y) = hp A k m (lmul A h m y)
  | 0, y => by simp [hp]
  | m + 1, y => by
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add (f := _), hf, hg]
    | single x a =>
      rw [lmul_single]
      simp only [hp, Finsupp.linearCombination_single, map_smul]
      rw [lmul_cone, map_sub, lmul_rmul, lmul_hp h k m, lmul_single, lmul_single]
      rfl

private theorem lmul_hd (h k k' : G) : ∀ (m : ℕ) (y : Ch A G m),
    lmul A h (m + 2) (hd A k k' m y) = hd A k k' m (lmul A h m y)
  | 0, y => by simp [hd]
  | m + 1, y => by
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add (f := _), hf, hg]
    | single x a =>
      rw [lmul_single]
      simp only [hd, Finsupp.linearCombination_single, map_smul]
      rw [lmul_cone, map_add (f := _), lmul_hp, lmul_rmul, lmul_hd h k k' m, lmul_single, lmul_single]
      rfl

end

theorem UpperTheory.leftMulChain_chainHomotopic :
    ∀ (A : Type) [CommRing A] (G : Type) [Group G] (k k' h : G) (m : ℕ) (z : Ch A G (m + 1)), pr A G (m + 2) (hd A k k' (m + 1) (lmul A h (m + 1) z)) = pr A G (m + 2) (hd A k k' (m + 1) z) := by
  intro A _ G _ k k' h m z
  rw [← lmul_hd]
  exact pr_lmul A h (m + 2) _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.TupleChainBoundaryFormula
section
open UpperTheory.V.ZK.PM
open UpperTheory.V.ZK hiding cone

private theorem hbd_eq (A : Type) [CommRing A] (G : Type) [Group G] :
    ∀ (m : ℕ) (z : Ch A G (m + 1)), PM.hbd A G m z = UpperTheory.V.ZK.hbd A G m z
  | 0, z => ch_ext A (fun x => by
      have h := hbd_cone_zero A (x 0) (Finsupp.single (Fin.tail (α := fun _ => G) x) 1)
      rw [cone_single, Fin.cons_self_tail] at h
      rw [h, PM.hbd, Finsupp.linearCombination_single, one_smul]) z
  | m + 1, z => ch_ext A (fun x => by
      have h := hbd_cone A (x 0) m (Finsupp.single (Fin.tail (α := fun _ => G) x) 1)
      rw [cone_single, Fin.cons_self_tail] at h
      rw [h, PM.hbd, Finsupp.linearCombination_single, one_smul, hbd_eq A G m]
      rfl) z

theorem UpperTheory.tupleChain_boundary_formula :
    ∀ (A : Type) [CommRing A] (G : Type) [Group G] (m : ℕ) (z : Ch A G (m + 2)), bd A G m (pr A G (m + 1) z) = pr A G m (PM.hbd A G (m + 1) z) := by
  intro A _ G _ m z
  rw [hbd_eq]
  exact bd_toInh A m z
end

