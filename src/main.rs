use std::time::{Duration};

const DURATION: Duration = Duration::from_secs(1);

fn main() {
    println!("Hello, world!");

    println!("On mesure le plus grand nombre de Fibonacci calculé en 1 seconde et l'index de ce nombre dans la liste sur plusieurs fonctions");

    let result_naif = fibo_functions::measure_fibonacci_naif();
    println!(
        "Le plus haut numéro de la suite de Fibonacci (naïf) calculé en 1 seconde : {} (index: {})",
        result_naif.1, result_naif.0
    );
    if verification::is_fibonacci(&result_naif.1) {
        println!("Ce nombre est bien dans la suite de Fibonacci (naïf).\n\n");
    } else {
        println!("Ce nombre n'est pas dans la suite de Fibonacci (naïf).\n\n");
    }

    let result_rec = fibo_functions::measure_fibonacci_recursive();
    println!(
        "Le plus haut numéro de la suite de Fibonacci (récursif) calculé en 1 seconde : {} (index: {})",
        result_rec.1, result_rec.0
    );
    if verification::is_fibonacci(&result_rec.1) {
        println!("Ce nombre est bien dans la suite de Fibonacci (récursif).\n\n");
    } else {
        println!("Ce nombre n'est pas dans la suite de Fibonacci (récursif).\n\n");
    }

    let result_memo = fibo_functions::measure_fibonacci_recursive_memo();
    println!(
        "Le plus haut numéro de la suite de Fibonacci (récursif avec mémoïsation) calculé en 1 seconde : {} (index: {})",
        result_memo.1, result_memo.0
    );
    if verification::is_fibonacci(&result_memo.1) {
        println!("Ce nombre est bien dans la suite de Fibonacci (récursif avec mémoïsation).\n\n");
    } else {
        println!("Ce nombre n'est pas dans la suite de Fibonacci (récursif avec mémoïsation).\n\n");
    }

    let result_doubling = fibo_functions::measure_fibonacci_doubling();
    println!(
        "Le plus haut numéro de la suite de Fibonacci (Doubling) calculé en 1 seconde : {} (index: {})",
        result_doubling.1, result_doubling.0
    );
    if verification::is_fibonacci(&result_doubling.1) {
        println!("Ce nombre est bien dans la suite de Fibonacci (Doubling).\n\n");
    } else {
        println!("Ce nombre n'est pas dans la suite de Fibonacci (Doubling).\n\n");
    }

    let best_algorithm = verification::select_best_algorithm(vec![
        ("Naïf", result_naif.0),
        ("Récursif", result_rec.0),
        ("Récursif avec Mémoïsation", result_memo.0),
        ("Doubling", result_doubling.0),
    ]);

    println!("Le meilleur algorithme pour cette machine est : {}", best_algorithm);
}

/// Module avec différentes implémentations de la suite de Fibonnaci
mod fibo_functions {
    use std::time::Instant;
    use num_bigint::BigUint;
    use num_traits::{One, Zero};
    use std::collections::HashMap;
    use crate::DURATION;

    /// Cette fonction mesure le plus grand nombre de Fibonacci calculé en 1 seconde et retourne l'index et la valeur.
    pub fn measure_fibonacci_naif() -> (usize, BigUint) {
        let start = Instant::now();
        let mut a: BigUint = BigUint::zero();
        let mut b: BigUint = BigUint::one();
        let mut index = 1;

        while Instant::now().duration_since(start) < DURATION {
            let next = &a + &b;
            a = b;
            b = next;
            index += 1;
        }

        (index, b)
    }

    /// Cette fonction mesure le plus grand nombre de Fibonacci calculé en 1 seconde avec l'algorithme récursif.
    pub fn measure_fibonacci_recursive() -> (usize, BigUint) {
        let start = Instant::now();
        let mut index = 0;
        let mut last_value = BigUint::zero();

        while Instant::now().duration_since(start) < DURATION {
            last_value = fibo_recursive(index);
            index += 1;
        }

        (index, last_value)
    }

    /// Fonction récursive naïve pour calculer Fibonacci.
    fn fibo_recursive(n: usize) -> BigUint {
        if n == 0 {
            BigUint::zero()
        } else if n == 1 {
            BigUint::one()
        } else {
            fibo_recursive(n - 1) + fibo_recursive(n - 2)
        }
    }

    /// Cette fonction mesure le plus grand nombre de Fibonacci calculé en 1 seconde avec l'algorithme récursif et mémoïsation.
    pub fn measure_fibonacci_recursive_memo() -> (usize, BigUint) {
        let start = Instant::now();
        let mut index = 0;
        let mut last_value = BigUint::zero();
        let mut memo: HashMap<usize, BigUint> = HashMap::new();

        while Instant::now().duration_since(start) < DURATION {
            last_value = fibo_recursive_memo(index, &mut memo).clone();
            index += 1;
        }

        (index, last_value)
    }

    /// Fonction récursive pour calculer Fibonacci avec mémoïsation
    fn fibo_recursive_memo(n: usize, memo: &mut HashMap<usize, BigUint>) -> BigUint {
        if let Some(value) = memo.get(&n) {
            return value.clone();
        }

        let result = if n == 0 {
            BigUint::zero()
        } else if n == 1 {
            BigUint::one()
        } else {
            let a = fibo_recursive_memo(n - 1, memo);
            let b = fibo_recursive_memo(n - 2, memo);
            a + b
        };

        memo.insert(n, result.clone());
        result
    }



    /// Cette fonction mesure le plus grand nombre de Fibonacci calculé en 1 seconde avec la méthode de Doubling.
    pub fn measure_fibonacci_doubling() -> (usize, BigUint) {
        let start = Instant::now();
        let mut index = 0;
        let mut last_value = BigUint::zero();

        while Instant::now().duration_since(start) < DURATION {
            last_value = fibo_doubling(index);
            index += 1;
        }

        (index, last_value)
    }

    /// Fonction qui calcule le n-ième nombre de Fibonacci en utilisant la méthode de Doubling.
    fn fibo_doubling(n: usize) -> BigUint {
        if n == 0 {
            return BigUint::zero();
        }
        if n == 1 {
            return BigUint::one();
        }

        let (fib_n, _) = fibo_doubling_helper(n);
        fib_n
    }

    /// Fonction d'aide qui calcule F(n) et F(n-1) en utilisant la méthode de Doubling.
    fn fibo_doubling_helper(n: usize) -> (BigUint, BigUint) {
        if n == 0 {
            (BigUint::zero(), BigUint::one())
        } else {
            let (a, b) = fibo_doubling_helper(n >> 1);
            let c = &a * (&b << 1) - &a * &a; // F(2k) = F(k) * (2F(k + 1) - F(k))
            let d = &a * &a + &b * &b; // F(2k + 1) = F(k)^2 + F(k + 1)^2

            if n % 2 == 0 {
                (c, d) // n est pair
            } else {
                (d.clone(), c + d) // n est impair
            }
        }
    }
}

/// Module qui va servir à vérifier qu'une valeur est bien dans la suite de Fibonacci
mod verification {
    use num_bigint::BigUint;

    /// Vérifie si un nombre est dans la suite de Fibonacci.
    pub fn is_fibonacci(n: &BigUint) -> bool {
        let square1 = BigUint::from(5u32) * n * n + BigUint::from(4u32);
        let square2 = BigUint::from(5u32) * n * n - BigUint::from(4u32);

        is_perfect_square(&square1) || is_perfect_square(&square2)
    }

    /// Vérifie si un nombre est un carré parfait.
    fn is_perfect_square(x: &BigUint) -> bool {
        let sqrt = x.sqrt();
        &sqrt * &sqrt == *x
    }

    /// Sélectionne l'algorithme le plus performant en fonction du nombre d'indices atteints.
    pub fn select_best_algorithm(results: Vec<(&str, usize)>) -> &str {
        let mut best_name = "";
        let mut best_index = 0;

        for (name, index) in results {
            if index > best_index {
                best_name = name;
                best_index = index;
            }
        }

        best_name
    }
}
