struct Matrix {
    Matrix() {}
};

Matrix identity() { return Matrix(); }

struct State {
    Matrix initial;
    State() : initial(identity()) {}
};

State make() {
    return State();
}

